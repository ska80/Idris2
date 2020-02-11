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

import Utils.Hex

import Data.NameMap
import Data.Vect
import System
import System.Info


%default covering


findLispWorks : IO String
findLispWorks
    = do e <- firstExists [p ++ x | p <- ["/usr/bin/", "/usr/local/bin/"],
                                    x <- ["lispworks", "lw"]]
         maybe (pure "/usr/bin/env lispworks") pure e


lspHeader : String
lspHeader = "\n\n"
         ++ "(in-package #:cl-user)\n\n"
         ++ "(declaim #.idris:*global-optimize-settings*)\n\n"


lspFooter : String
lspFooter = ""


showLispworksChar : Char -> String -> String
showLispworksChar '\\' = ("\\\\" ++)
showLispworksChar c
   = if c < chr 32 || c > chr 126
        then (("\\u" ++ pad (asHex (cast c))) ++)
        else strCons c
  where
    pad : String -> String
    pad str
        = case isLTE (length str) 4 of
               Yes _ => cast (List.replicate (4 - length str) '0') ++ str
               No _ => str


showLispworksString : List Char -> String -> String
showLispworksString [] = id
showLispworksString ('"' :: cs) = ("\\\"" ++) . showLispworksString cs
showLispworksString (c :: cs) = (showLispworksChar c) . showLispworksString cs


lispworksString : String -> String
lispworksString cs = strCons '"' (showLispworksString (unpack cs) "\"")


lispworksPrim : Int -> SVars vars -> ExtPrim -> List (CExp vars) -> Core String
lispworksPrim i vs CCall [ret, fn, fargs, world]
  = throw (InternalError ("Can't compile C FFI calls to LispWorks yet"))
lispworksPrim i vs SysCodegen []
  = pure $ "\"lispworks\""
lispworksPrim i vs prim args
  = lspExtCommon lispworksPrim lispworksString i vs prim args


||| Compile a TT expression to LispWorks
compileToLISP : Ref Ctxt Defs ->
              ClosedTerm -> (outfile : String) -> Core ()
compileToLISP c tm outfile
    = do ds <- getDirectives LispWorks
         (ns, tags) <- findUsedNames tm
         defs <- get Ctxt
         compdefs <- traverse (getLisp lispworksPrim lispworksString defs) ns
         let code = concat compdefs
         main <- lspExp lispworksPrim lispworksString 0 [] !(compileExp tags tm)
         lispworks <- coreLift findLispWorks
         support <- readDataFile "lispworks/support.lisp"
         let lisp = support ++ lspHeader ++ code ++ main ++ lspFooter
         Right () <- coreLift $ writeFile outfile lisp
            | Left err => throw (FileErr outfile err)
         coreLift $ chmod outfile 0o644
         pure ()


||| LispWorks implementation of the `compileExpr` interface.
compileExpr : Ref Ctxt Defs ->
              ClosedTerm -> (outfile : String) -> Core (Maybe String)
compileExpr c tm outfile
    = do let outn = outfile ++ ".lisp"
         compileToLISP c tm outn
         pure (Just outn)


||| LispWorks implementation of the `executeExpr` interface.
||| This implementation simply runs the usual compiler, saving it to a temp file, then interpreting it.
executeExpr : Ref Ctxt Defs -> ClosedTerm -> Core ()
executeExpr c tm
    = do tmp <- coreLift $ tmpName
         let outn = tmp ++ ".lisp"
         compileToLISP c tm outn
         lispworks <- coreLift findLispWorks
         coreLift $ system $ lispworks
                             ++ " -siteinit - -init - --load "
                             ++ outn
                             ++ " -eval '(lw:quit :status 0)'"
         pure ()


||| Codegen wrapper for LispWorks implementation.
export
codegenLispWorks : Codegen
codegenLispWorks = MkCG compileExpr executeExpr
