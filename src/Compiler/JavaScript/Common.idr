module Compiler.JavaScript.Common


import Compiler.Common
import Compiler.CompileExpr
import Compiler.Inline

import Core.Context
import Core.Name
import Core.TT

import Data.List
import Data.Vect

import System.Info


%default covering


export
firstExists : List String -> IO (Maybe String)
firstExists [] = pure Nothing
firstExists (x :: xs) = if !(exists x)
                           then pure (Just x)
                           else firstExists xs


jsString : String -> String
jsString s = concatMap okchar (unpack s)
  where
    okchar : Char -> String
    okchar c = if isAlphaNum c || c == '_'
                  then cast c
                  else "C_" ++ show (cast {to = Int} c)


export
jsName : Name -> String
jsName (NS ns n) = "ns_" ++ showSep "_" ns ++ "_" ++ jsName n
jsName (UN n) = jsString n
jsName (MN n i) = jsString n ++ "_" ++ show i
jsName (PV n d) = "pat__" ++ jsName n
jsName (DN _ n) = jsName n
jsName (Nested i n) = "n__" ++ show i ++ "_" ++ jsName n
jsName (CaseBlock x y) = "case__" ++ show x ++ "_" ++ show y
jsName (WithBlock x y) = "with__" ++ show x ++ "_" ++ show y
jsName (Resolved i) = "fn__" ++ show i


public export
data SVars : List Name -> Type where
     Nil : SVars []
     (::) : (svar : String) -> SVars ns -> SVars (n :: ns)


extendSVars : (xs : List Name) -> SVars ns -> SVars (xs ++ ns)
extendSVars {ns} xs vs = extSVars' (cast (length ns)) xs vs
  where
    extSVars' : Int -> (xs : List Name) -> SVars ns -> SVars (xs ++ ns)
    extSVars' i [] vs = vs
    extSVars' i (x :: xs) vs = jsName (MN "v" i) :: extSVars' (i + 1) xs vs


export
initSVars : (xs : List Name) -> SVars xs
initSVars xs = rewrite sym (appendNilRightNeutral xs) in extendSVars xs []


lookupSVar : {idx : Nat} -> .(IsVar n idx xs) -> SVars xs -> String
lookupSVar First (n :: ns) = n
lookupSVar (Later p) (n :: ns) = lookupSVar p ns


export
jsConstructor : Int -> List String -> String
jsConstructor t args = "{tag: " ++ show t ++ ", args: [" ++ showSep ", " args ++ "]}"


wrap : String -> String
wrap e = "(" ++ e ++ ")"


fun : String -> List String -> String
fun f args = f ++ (wrap $ showSep ", " args)


meth : String -> List String -> String -> String
meth m args x = wrap x ++ "." ++ fun m args


prop : String -> String -> String
prop p x = wrap x ++ "." ++ p


index : String -> String -> String
index i x = wrap x ++ "[" ++ i ++ "]"


uop : String -> String -> String
uop o x = wrap $ showSep "" [o, x]


bop : String -> String -> String -> String
bop o x y = wrap $ showSep " " [x, o, y]


boolop : String -> String
boolop o = wrap $ o ++ " ? 1 : 0"


jsOp : PrimFn arity -> Vect arity String -> String
jsOp (Add IntType) [x, y] = fun "IDRIS.intAdd" [x, y]
jsOp (Sub IntType) [x, y] = fun "IDRIS.intSub" [x, y]
jsOp (Mul IntType) [x, y] = fun "IDRIS.intMul" [x, y]
jsOp (Div IntType) [x, y] = fun "IDRIS.intDiv" [x, y]
jsOp (Add ty) [x, y] = bop "+" x y
jsOp (Sub ty) [x, y] = bop "-" x y
jsOp (Mul ty) [x, y] = bop "*" x y
jsOp (Div ty) [x, y] = bop "/" x y
jsOp (Mod ty) [x, y] = bop "%" x y
jsOp (Neg ty) [x] = uop "-" x
jsOp (ShiftL ty) [x, y] = bop "<<" x y
jsOp (ShiftR ty) [x, y] = bop ">>" x y
jsOp (BAnd ty) [x, y] = bop "&" x y
jsOp (BOr ty) [x, y] = bop "|" x y
jsOp (BXOr ty) [x, y] = bop "^" x y
jsOp (LT ty) [x, y] = boolop $ bop "<" x y
jsOp (LTE ty) [x, y] = boolop $ bop "<=" x y
jsOp (EQ ty) [x, y] = boolop $ bop "===" x y
jsOp (GTE ty) [x, y] = boolop $ bop ">=" x y
jsOp (GT ty) [x, y] = boolop $ bop ">" x y
jsOp StrLength [x] = prop "length" x
jsOp StrHead [x] = index "0" x
jsOp StrTail [x] = meth "slice" ["1"] x
jsOp StrIndex [x, i] = index i x
jsOp StrCons [x, y] = bop "+" x y
jsOp StrAppend [x, y] = bop "+" x y
jsOp StrReverse [x] = (meth "join" ["''"] . meth "reverse" [] . meth "split" ["''"]) x
jsOp StrSubstr [x, y, z] = meth "substr" [y, z] x

-- `e` is Euler's number, which approximates to: 2.718281828459045
jsOp DoubleExp [x] = fun "Math.exp" [x] -- Base is `e`. Same as: `pow(e, x)`
jsOp DoubleLog [x] = fun "Math.log" [x] -- Base is `e`.
jsOp DoubleSin [x] = fun "Math.sin" [x]
jsOp DoubleCos [x] = fun "Math.cos" [x]
jsOp DoubleTan [x] = fun "Math.tan" [x]
jsOp DoubleASin [x] = fun "Math.asin" [x]
jsOp DoubleACos [x] = fun "Math.acos" [x]
jsOp DoubleATan [x] = fun "Math.atan" [x]
jsOp DoubleSqrt [x] = fun "Math.sqrt" [x]
jsOp DoubleFloor [x] = fun "Math.floor" [x]
jsOp DoubleCeiling [x] = fun "Math.ceil" [x]

jsOp (Cast IntType StringType) [x] = fun "IDRIS.intToString" [x]
jsOp (Cast IntegerType StringType) [x] = fun "IDRIS.integerToString" [x]
jsOp (Cast DoubleType StringType) [x] = fun "IDRIS.doubleToString" [x]
jsOp (Cast CharType StringType) [x] = fun "IDRIS.charToString" [x]

jsOp (Cast IntType IntegerType) [x] = fun "IDRIS.intToInteger" [x]
jsOp (Cast DoubleType IntegerType) [x] = fun "IDRIS.doubleToInteger" [x]
jsOp (Cast CharType IntegerType) [x] = fun "IDRIS.charToInteger" [x]
jsOp (Cast StringType IntegerType) [x] = fun "IDRIS.stringToInteger" [x]

jsOp (Cast IntegerType IntType) [x] = fun "IDRIS.integerToInt" [x]
jsOp (Cast DoubleType IntType) [x] = fun "IDRIS.doubleToInt" [x]
jsOp (Cast StringType IntType) [x] = fun "IDRIS.stringToInt" [x]
jsOp (Cast CharType IntType) [x] = fun "IDRIS.charToInt" [x]

jsOp (Cast IntegerType DoubleType) [x] = fun "IDRIS.integerToDouble" [x]
jsOp (Cast IntType DoubleType) [x] = fun "IDRIS.intToDouble" [x]
jsOp (Cast StringType DoubleType) [x] = fun "IDRIS.stringToDouble" [x]

jsOp (Cast IntType CharType) [x] = fun "IDRIS.intToChar" [x]

jsOp (Cast from to) [x] = fun "IDRIS.errorQuit" ["Invalid cast " ++ show from ++ "->" ++ show to]

jsOp BelieveMe [_, _, x] = x


public export
data ExtPrim = JsCall | PutStr | GetStr
             | FileOpen | FileClose | FileReadLine | FileWriteLine | FileEOF
             | NewIORef | ReadIORef | WriteIORef
             | NewArray | ArrayGet | ArraySet
             | Stdin | Stdout | Stderr
             | VoidElim
             | SysOS | SysCodegen
             | Unknown Name


export
Show ExtPrim where
  show JsCall = "JsCall"
  show PutStr = "PutStr"
  show GetStr = "GetStr"
  show FileOpen = "FileOpen"
  show FileClose = "FileClose"
  show FileReadLine = "FileReadLine"
  show FileWriteLine = "FileWriteLine"
  show FileEOF = "FileEOF"
  show NewIORef = "NewIORef"
  show ReadIORef = "ReadIORef"
  show WriteIORef = "WriteIORef"
  show NewArray = "NewArray"
  show ArrayGet = "ArrayGet"
  show ArraySet = "ArraySet"
  show Stdin = "Stdin"
  show Stdout = "Stdout"
  show Stderr = "Stderr"
  show VoidElim = "VoidElim"
  show SysOS = "SysOS"
  show SysCodegen = "SysCodegen"
  show (Unknown n) = "Unknown " ++ show n


toPrim : Name -> ExtPrim
toPrim pn@(NS _ n)
    = cond [(n == UN "prim__jsCall", JsCall),
            (n == UN "prim__putStr", PutStr),
            (n == UN "prim__getStr", GetStr),
            (n == UN "prim__open", FileOpen),
            (n == UN "prim__close", FileClose),
            (n == UN "prim__readLine", FileReadLine),
            (n == UN "prim__writeLine", FileWriteLine),
            (n == UN "prim__eof", FileEOF),
            (n == UN "prim__newIORef", NewIORef),
            (n == UN "prim__readIORef", ReadIORef),
            (n == UN "prim__writeIORef", WriteIORef),
            (n == UN "prim__newArray", NewArray),
            (n == UN "prim__arrayGet", ArrayGet),
            (n == UN "prim__arraySet", ArraySet),
            (n == UN "prim__stdin", Stdin),
            (n == UN "prim__stdout", Stdout),
            (n == UN "prim__stderr", Stderr),
            (n == UN "void", VoidElim),
            (n == UN "prim__os", SysOS),
            (n == UN "prim__codegen", SysCodegen)
            ]
           (Unknown pn)
toPrim pn = Unknown pn


export
mkWorld : String -> String
mkWorld res = jsConstructor 0 ["false", res, "false"] -- MkIORes


toHex : Char -> String
toHex c = substr 2 6 (b32ToHexString (fromInteger (cast (ord c))))


jsConstant : (String -> String) -> Constant -> String
jsConstant _ (I x) = show x
jsConstant _ (BI x) = show x
jsConstant jsString (Str x) = "'" ++ jsString x ++ "'"
jsConstant _ (Ch x) = "'\\u" ++ toHex x ++ "'"
jsConstant _ (Db x) = show x
jsConstant _ WorldVal = "false"
jsConstant _ IntType = "true"
jsConstant _ IntegerType = "true"
jsConstant _ StringType = "true"
jsConstant _ CharType = "true"
jsConstant _ DoubleType = "true"
jsConstant _ WorldType = "true"


{-
schCaseDef : Maybe String -> String
schCaseDef Nothing = ""
schCaseDef (Just tm) = "(else " ++ tm ++ ")"

export
schArglist : SVars ns -> String
schArglist [] = ""
schArglist [x] = x
schArglist (x :: xs) = x ++ " " ++ schArglist xs

parameters (schExtPrim : {vars : _} -> Int -> SVars vars -> ExtPrim -> List (CExp vars) -> Core String,
            schString : String -> String)
  mutual
    schConAlt : Int -> SVars vars -> String -> CConAlt vars -> Core String
    schConAlt {vars} i vs target (MkConAlt n tag args sc)
        = let vs' = extendSVars args vs in
              pure $ "((" ++ show tag ++ ") "
                          ++ bindArgs 1 args vs' !(schExp i vs' sc) ++ ")"
      where
        bindArgs : Int -> (ns : List Name) -> SVars (ns ++ vars) -> String -> String
        bindArgs i [] vs body = body
        bindArgs i (n :: ns) (v :: vs) body
            = "(let ((" ++ v ++ " " ++ "(vector-ref " ++ target ++ " " ++ show i ++ "))) "
                    ++ bindArgs (i + 1) ns vs body ++ ")"

    schConstAlt : Int -> SVars vars -> String -> CConstAlt vars -> Core String
    schConstAlt i vs target (MkConstAlt c exp)
        = pure $ "((equal? " ++ target ++ " " ++ schConstant schString c ++ ") " ++ !(schExp i vs exp) ++ ")"

    -- oops, no traverse for Vect in Core
    schArgs : Int -> SVars vars -> Vect n (CExp vars) -> Core (Vect n String)
    schArgs i vs [] = pure []
    schArgs i vs (arg :: args) = pure $ !(schExp i vs arg) :: !(schArgs i vs args)

    export
    schExp : Int -> SVars vars -> CExp vars -> Core String
    schExp i vs (CLocal fc el) = pure $ lookupSVar el vs
    schExp i vs (CRef fc n) = pure $ schName n
    schExp i vs (CLam fc x sc)
       = do let vs' = extendSVars [x] vs
            sc' <- schExp i vs' sc
            pure $ "(lambda (" ++ lookupSVar First vs' ++ ") " ++ sc' ++ ")"
    schExp i vs (CLet fc x val sc)
       = do let vs' = extendSVars [x] vs
            val' <- schExp i vs val
            sc' <- schExp i vs' sc
            pure $ "(let ((" ++ lookupSVar First vs' ++ " " ++ val' ++ ")) " ++ sc' ++ ")"
    schExp i vs (CApp fc x [])
        = pure $ "(" ++ !(schExp i vs x) ++ ")"
    schExp i vs (CApp fc x args)
        = pure $ "(" ++ !(schExp i vs x) ++ " " ++ showSep " " !(traverse (schExp i vs) args) ++ ")"
    schExp i vs (CCon fc x tag args)
        = pure $ schConstructor tag !(traverse (schExp i vs) args)
    schExp i vs (COp fc op args)
        = pure $ schOp op !(schArgs i vs args)
    schExp i vs (CExtPrim fc p args)
        = schExtPrim i vs (toPrim p) args
    schExp i vs (CForce fc t) = pure $ "(force " ++ !(schExp i vs t) ++ ")"
    schExp i vs (CDelay fc t) = pure $ "(delay " ++ !(schExp i vs t) ++ ")"
    schExp i vs (CConCase fc sc alts def)
        = do tcode <- schExp (i+1) vs sc
             defc <- maybe (pure Nothing) (\v => pure (Just !(schExp i vs v))) def
             let n = "sc" ++ show i
             pure $ "(let ((" ++ n ++ " " ++ tcode ++ ")) (case (get-tag " ++ n ++ ") "
                     ++ showSep " " !(traverse (schConAlt (i+1) vs n) alts)
                     ++ schCaseDef defc ++ "))"
    schExp i vs (CConstCase fc sc alts def)
        = do defc <- maybe (pure Nothing) (\v => pure (Just !(schExp i vs v))) def
             tcode <- schExp (i+1) vs sc
             let n = "sc" ++ show i
             pure $ "(let ((" ++ n ++ " " ++ tcode ++ ")) (cond "
                      ++ showSep " " !(traverse (schConstAlt (i+1) vs n) alts)
                      ++ schCaseDef defc ++ "))"
    schExp i vs (CPrimVal fc c) = pure $ schConstant schString c
    schExp i vs (CErased fc) = pure "'()"
    schExp i vs (CCrash fc msg) = pure $ "(blodwen-error-quit " ++ show msg ++ ")"

  -- Need to convert the argument (a list of scheme arguments that may
  -- have been constructed at run time) to a scheme list to be passed to apply
  readArgs : Int -> SVars vars -> CExp vars -> Core String
  readArgs i vs tm = pure $ "(blodwen-read-args " ++ !(schExp i vs tm) ++ ")"

  fileOp : String -> String
  fileOp op = "(blodwen-file-op (lambda () " ++ op ++ "))"

  -- External primitives which are common to the scheme codegens (they can be
  -- overridden)
  export
  schExtCommon : Int -> SVars vars -> ExtPrim -> List (CExp vars) -> Core String
  schExtCommon i vs SchemeCall [ret, CPrimVal fc (Str fn), args, world]
     = pure $ mkWorld ("(apply " ++ fn ++" "
                  ++ !(readArgs i vs args) ++ ")")
  schExtCommon i vs SchemeCall [ret, fn, args, world]
       = pure $ mkWorld ("(apply (eval (string->symbol " ++ !(schExp i vs fn) ++")) "
                    ++ !(readArgs i vs args) ++ ")")
  schExtCommon i vs PutStr [arg, world]
      = pure $ "(display " ++ !(schExp i vs arg) ++ ") " ++ mkWorld (schConstructor 0 []) -- code for MkUnit
  schExtCommon i vs GetStr [world]
      = pure $ mkWorld "(blodwen-get-line (current-input-port))"
  schExtCommon i vs FileOpen [file, mode, bin, world]
      = pure $ mkWorld $ fileOp $ "(blodwen-open "
                                      ++ !(schExp i vs file) ++ " "
                                      ++ !(schExp i vs mode) ++ " "
                                      ++ !(schExp i vs bin) ++ ")"
  schExtCommon i vs FileClose [file, world]
      = pure $ "(blodwen-close-port " ++ !(schExp i vs file) ++ ") " ++ mkWorld (schConstructor 0 [])
  schExtCommon i vs FileReadLine [file, world]
      = pure $ mkWorld $ fileOp $ "(blodwen-get-line " ++ !(schExp i vs file) ++ ")"
  schExtCommon i vs FileWriteLine [file, str, world]
      = pure $ mkWorld $ fileOp $ "(blodwen-putstring "
                                        ++ !(schExp i vs file) ++ " "
                                        ++ !(schExp i vs str) ++ ")"
  schExtCommon i vs FileEOF [file, world]
      = pure $ mkWorld $ "(blodwen-eof " ++ !(schExp i vs file) ++ ")"
  schExtCommon i vs NewIORef [_, val, world]
      = pure $ mkWorld $ "(box " ++ !(schExp i vs val) ++ ")"
  schExtCommon i vs ReadIORef [_, ref, world]
      = pure $ mkWorld $ "(unbox " ++ !(schExp i vs ref) ++ ")"
  schExtCommon i vs WriteIORef [_, ref, val, world]
      = pure $ mkWorld $ "(set-box! "
                           ++ !(schExp i vs ref) ++ " "
                           ++ !(schExp i vs val) ++ ")"
  schExtCommon i vs NewArray [_, size, val, world]
      = pure $ mkWorld $ "(make-vector " ++ !(schExp i vs size) ++ " "
                                         ++ !(schExp i vs val) ++ ")"
  schExtCommon i vs ArrayGet [_, arr, pos, world]
      = pure $ mkWorld $ "(vector-ref " ++ !(schExp i vs arr) ++ " "
                                        ++ !(schExp i vs pos) ++ ")"
  schExtCommon i vs ArraySet [_, arr, pos, val, world]
      = pure $ mkWorld $ "(vector-set! " ++ !(schExp i vs arr) ++ " "
                                         ++ !(schExp i vs pos) ++ " "
                                         ++ !(schExp i vs val) ++ ")"
  schExtCommon i vs VoidElim [_, _]
      = pure "(display \"Error: Executed 'void'\")"
  schExtCommon i vs SysOS []
      = pure $ show os
  schExtCommon i vs (Unknown n) args
      = throw (InternalError ("Can't compile unknown external primitive " ++ show n))
  schExtCommon i vs Stdin [] = pure "(current-input-port)"
  schExtCommon i vs Stdout [] = pure "(current-output-port)"
  schExtCommon i vs Stderr [] = pure "(current-error-port)"
  schExtCommon i vs prim args
      = throw (InternalError ("Badly formed external primitive " ++ show prim
                                ++ " " ++ show args))

  schDef : {auto c : Ref Ctxt Defs} ->
           Name -> CDef -> Core String
  schDef n (MkFun args exp)
     = let vs = initSVars args in
           pure $ "(define " ++ schName !(getFullName n) ++ " (lambda (" ++ schArglist vs ++ ") "
                      ++ !(schExp 0 vs exp) ++ "))\n"
  schDef n (MkError exp)
     = pure $ "(define (" ++ schName !(getFullName n) ++ " . any-args) " ++ !(schExp 0 [] exp) ++ ")\n"
  schDef n (MkForeign _ _ _) = pure "" -- compiled by specific back end
  schDef n (MkCon t a) = pure "" -- Nothing to compile here

-- Convert the name to scheme code
-- (There may be no code generated, for example if it's a constructor)
export
getScheme : {auto c : Ref Ctxt Defs} ->
            (schExtPrim : {vars : _} -> Int -> SVars vars -> ExtPrim -> List (CExp vars) -> Core String) ->
            (schString : String -> String) ->
            Defs -> Name -> Core String
getScheme schExtPrim schString defs n
    = case !(lookupCtxtExact n (gamma defs)) of
           Nothing => throw (InternalError ("Compiling undefined name " ++ show n))
           Just d => case compexpr d of
                          Nothing =>
                             throw (InternalError ("No compiled definition for " ++ show n))
                          Just d => schDef schExtPrim schString n d
-}
