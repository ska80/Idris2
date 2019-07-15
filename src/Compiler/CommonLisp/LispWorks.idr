module Compiler.CommonLisp.LispWorks

import Compiler.Common
import Compiler.CompileExpr
import Compiler.Inline
import Compiler.CommonLisp.Common

import Core.Context
import Core.Directory
import Core.Name
import Core.Options
import Core.TT

import Data.NameMap
import Data.Vect
import System
import System.Info

%default covering

firstExists : List String -> IO (Maybe String)
firstExists [] = pure Nothing
firstExists (x :: xs) = if !(exists x) then pure (Just x) else firstExists xs

findLispWorks : IO String
findLispWorks
    = do env <- getEnv "CHEZ"
         case env of
            Just n => pure n
            Nothing => do e <- firstExists [p ++ x | p <- ["/usr/bin/", "/usr/local/bin/"],
                                    x <- ["scheme", "chez", "chezscheme9.5"]]
                          maybe (pure "/usr/bin/env scheme") pure e

findLibs : List String -> List String
findLibs = mapMaybe (isLib . trim)
  where
    isLib : String -> Maybe String
    isLib d
        = if isPrefixOf "lib" d
             then Just (trim (substr 3 (length d) d))
             else Nothing

escapeQuotes : String -> String
escapeQuotes s = pack $ foldr escape [] $ unpack s
  where
    escape : Char -> List Char -> List Char
    escape '"' cs = '\\' :: '\"' :: cs
    escape c   cs = c :: cs

lspHeader : String -> List String -> String
lspHeader chez libs
  = (if os /= "windows" then "#!" ++ chez ++ " --script\n\n" else "") ++
    "(import (chezscheme))\n" ++
    "(case (machine-type)\n" ++
    "  [(i3le ti3le a6le ta6le) (load-shared-object \"libc.so.6\")]\n" ++
    "  [(i3osx ti3osx a6osx ta6osx) (load-shared-object \"libc.dylib\")]\n" ++
    "  [(i3nt ti3nt a6nt ta6nt) (load-shared-object \"msvcrt.dll\")]\n" ++
    "  [else (load-shared-object \"libc.so\")])\n\n" ++
    showSep "\n" (map (\x => "(load-shared-object \"" ++ escapeQuotes x ++ "\")") libs) ++ "\n\n" ++
    "(let ()\n"

lspFooter : String
lspFooter = ")"

mutual
  tySpec : CExp vars -> Core String
  tySpec (CPrimVal fc IntType) = pure "int"
  tySpec (CPrimVal fc StringType) = pure "string"
  tySpec (CPrimVal fc DoubleType) = pure "double"
  tySpec (CCon fc (NS _ n) _ [])
     = cond [(n == UN "Unit", pure "void"),
             (n == UN "Ptr", pure "void*")]
          (throw (InternalError ("Can't pass argument of type " ++ show n ++ " to foreign function")))
  tySpec ty = throw (InternalError ("Can't pass argument of type " ++ show ty ++ " to foreign function"))

  handleRet : String -> String -> String
  handleRet "void" op = op ++ " " ++ mkWorld (lspConstructor 0 [])
  handleRet _ op = mkWorld op

  getFArgs : CExp vars -> Core (List (CExp vars, CExp vars))
  getFArgs (CCon fc _ 0 _) = pure []
  getFArgs (CCon fc _ 1 [ty, val, rest]) = pure $ (ty, val) :: !(getFArgs rest)
  getFArgs arg = throw (GenericMsg (getFC arg) ("Badly formed c call argument list " ++ show arg))

  lispworksExtPrim : Int -> SVars vars -> ExtPrim -> List (CExp vars) -> Core String
  lispworksExtPrim i vs CCall [ret, CPrimVal fc (Str fn), fargs, world]
      = do args <- getFArgs fargs
           argTypes <- traverse tySpec (map fst args)
           retType <- tySpec ret
           argsc <- traverse (lspExp lispworksExtPrim 0 vs) (map snd args)
           pure $ handleRet retType ("((foreign-procedure #f " ++ show fn ++ " ("
                    ++ showSep " " argTypes ++ ") " ++ retType ++ ") "
                    ++ showSep " " argsc ++ ")")
  lispworksExtPrim i vs CCall [ret, fn, args, world]
      = pure "(error \"bad ffi call\")"
      -- throw (InternalError ("C FFI calls must be to statically known functions (" ++ show fn ++ ")"))
  lispworksExtPrim i vs GetStr [world]
      = pure $ mkWorld "(get-line (current-input-port))"
  lispworksExtPrim i vs prim args
      = lspExtCommon lispworksExtPrim i vs prim args

||| Compile a TT expression to Chez Scheme
compileToSS : Ref Ctxt Defs ->
              ClosedTerm -> (outfile : String) -> Core ()
compileToSS c tm outfile
    = do ds <- getDirectives Chez
         let libs = findLibs ds
         (ns, tags) <- findUsedNames tm
         defs <- get Ctxt
         compdefs <- traverse (getLisp lispworksExtPrim defs) ns
         let code = concat compdefs
         main <- lspExp lispworksExtPrim 0 [] !(compileExp tags tm)
         lispworks <- coreLift findLispWorks
         support <- readDataFile "chez/support.ss"
         let lisp = lspHeader lispworks libs ++ support ++ code ++ main ++ lspFooter
         Right () <- coreLift $ writeFile outfile lisp
            | Left err => throw (FileErr outfile err)
         coreLift $ chmod outfile 0o755
         pure ()


||| Chez Scheme implementation of the `compileExpr` interface.
compileExpr : Ref Ctxt Defs ->
              ClosedTerm -> (outfile : String) -> Core (Maybe String)
compileExpr c tm outfile
    = do let outn = outfile ++ ".ss"
         compileToSS c tm outn
         -- TODO: Compile to .so too?
         pure (Just outn)

||| Chez Scheme implementation of the `executeExpr` interface.
||| This implementation simply runs the usual compiler, saving it to a temp file, then interpreting it.
executeExpr : Ref Ctxt Defs -> ClosedTerm -> Core ()
executeExpr c tm
    = do tmp <- coreLift $ tmpName
         let outn = tmp ++ ".ss"
         compileToSS c tm outn
         lispworks <- coreLift findLispWorks
         coreLift $ system (lispworks ++ " --script " ++ outn)
         pure ()

||| Codegen wrapper for LispWorks implementation.
export
codegenLispWorks : Codegen
codegenLispWorks = MkCG compileExpr executeExpr
