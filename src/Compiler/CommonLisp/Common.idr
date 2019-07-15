module Compiler.CommonLisp.Common

import Compiler.Common
import Compiler.CompileExpr
import Compiler.Inline

import Core.Context
import Core.Name
import Core.TT

import Data.List
import Data.Vect

%default covering

lspString : String -> String
lspString s = concatMap okchar (unpack s)
  where
    okchar : Char -> String
    okchar c = if isAlphaNum c || c =='_'
                  then cast c
                  else "C-" ++ show (cast {to=Int} c)

lspName : Name -> String
lspName (NS ns n) = showSep "-" ns ++ "-" ++ lspName n
lspName (UN n) = lspString n
lspName (MN n i) = lspString n ++ "-" ++ show i
lspName (PV n d) = "pat--" ++ lspName n
lspName (DN _ n) = lspName n
lspName (Nested i n) = "n--" ++ show i ++ "-" ++ lspName n
lspName (CaseBlock x y) = "case--" ++ show x ++ "-" ++ show y
lspName (WithBlock x y) = "with--" ++ show x ++ "-" ++ show y
lspName (Resolved i) = "fn--" ++ show i

-- local variable names as lisp names - we need to invent new names for the locals
-- because there might be shadows in the original expression which can't be resolved
-- by the same scoping rules. (e.g. something that computes \x, x => x + x where the
-- names are the same but refer to different bindings in the scope)
public export
data SVars : List Name -> Type where
     Nil : SVars []
     (::) : (svar : String) -> SVars ns -> SVars (n :: ns)

extendSVars : (xs : List Name) -> SVars ns -> SVars (xs ++ ns)
extendSVars {ns} xs vs = extSVars' (cast (length ns)) xs vs
  where
    extSVars' : Int -> (xs : List Name) -> SVars ns -> SVars (xs ++ ns)
    extSVars' i [] vs = vs
    extSVars' i (x :: xs) vs = lspName (MN "v" i) :: extSVars' (i + 1) xs vs

initSVars : (xs : List Name) -> SVars xs
initSVars xs = rewrite sym (appendNilRightNeutral xs) in extendSVars xs []

lookupSVar : {idx : Nat} -> .(IsVar n idx xs) -> SVars xs -> String
lookupSVar First (n :: ns) = n
lookupSVar (Later p) (n :: ns) = lookupSVar p ns

export
lspConstructor : Int -> List String -> String
lspConstructor t args = "(vector " ++ show t ++ " " ++ showSep " " args ++ ")"

||| Generate lisp for a plain function.
op : String -> List String -> String
op o args = "(" ++ o ++ " " ++ showSep " " args ++ ")"

||| Generate lisp for a boolean operation.
boolop : String -> List String -> String
boolop o args = "(or (and " ++ op o args ++ " 1) 0)"

||| Generate lisp for a primitive function.
lspOp : PrimFn arity -> Vect arity String -> String
lspOp (Add IntType) [x, y] = op "b+" [x, y, "63"]
lspOp (Sub IntType) [x, y] = op "b-" [x, y, "63"]
lspOp (Mul IntType) [x, y] = op "b*" [x, y, "63"]
lspOp (Div IntType) [x, y] = op "b/" [x, y, "63"]
lspOp (Add ty) [x, y] = op "+" [x, y]
lspOp (Sub ty) [x, y] = op "-" [x, y]
lspOp (Mul ty) [x, y] = op "*" [x, y]
lspOp (Div ty) [x, y] = op "/" [x, y]
lspOp (Mod ty) [x, y] = op "remainder" [x, y]
lspOp (Neg ty) [x] = op "-" [x]
lspOp (ShiftL ty) [x, y] = op "blodwen-shl" [x, y]
lspOp (ShiftR ty) [x, y] = op "blodwen-shr" [x, y]
lspOp (LT CharType) [x, y] = boolop "char<?" [x, y]
lspOp (LTE CharType) [x, y] = boolop "char<=?" [x, y]
lspOp (EQ CharType) [x, y] = boolop "char=?" [x, y]
lspOp (GTE CharType) [x, y] = boolop "char>=?" [x, y]
lspOp (GT CharType) [x, y] = boolop "char>?" [x, y]
lspOp (LT StringType) [x, y] = boolop "string<?" [x, y]
lspOp (LTE StringType) [x, y] = boolop "string<=?" [x, y]
lspOp (EQ StringType) [x, y] = boolop "string=?" [x, y]
lspOp (GTE StringType) [x, y] = boolop "string>=?" [x, y]
lspOp (GT StringType) [x, y] = boolop "string>?" [x, y]
lspOp (LT ty) [x, y] = boolop "<" [x, y]
lspOp (LTE ty) [x, y] = boolop "<=" [x, y]
lspOp (EQ ty) [x, y] = boolop "=" [x, y]
lspOp (GTE ty) [x, y] = boolop ">=" [x, y]
lspOp (GT ty) [x, y] = boolop ">" [x, y]
lspOp StrLength [x] = op "string-length" [x]
lspOp StrHead [x] = op "string-ref" [x, "0"]
lspOp StrTail [x] = op "substring" [x, "1", op "string-length" [x]]
lspOp StrIndex [x, i] = op "string-ref" [x, i]
lspOp StrCons [x, y] = op "string-cons" [x, y]
lspOp StrAppend [x, y] = op "string-append" [x, y]
lspOp StrReverse [x] = op "string-reverse" [x]
lspOp StrSubstr [x, y, z] = op "string-substr" [x, y, z]

lspOp DoubleExp [x] = op "exp" [x]
lspOp DoubleLog [x] = op "log" [x]
lspOp DoubleSin [x] = op "sin" [x]
lspOp DoubleCos [x] = op "cos" [x]
lspOp DoubleTan [x] = op "tan" [x]
lspOp DoubleASin [x] = op "asin" [x]
lspOp DoubleACos [x] = op "asin" [x]
lspOp DoubleATan [x] = op "atan" [x]
lspOp DoubleSqrt [x] = op "sqrt" [x]
lspOp DoubleFloor [x] = op "floor" [x]
lspOp DoubleCeiling [x] = op "ceiling" [x]

lspOp (Cast IntType StringType) [x] = op "number->string" [x]
lspOp (Cast IntegerType StringType) [x] = op "number->string" [x]
lspOp (Cast DoubleType StringType) [x] = op "number->string" [x]
lspOp (Cast CharType StringType) [x] = op "string" [x]

lspOp (Cast IntType IntegerType) [x] = x
lspOp (Cast DoubleType IntegerType) [x] = op "floor" [x]
lspOp (Cast CharType IntegerType) [x] = op "char->integer" [x]
lspOp (Cast StringType IntegerType) [x] = op "cast-string-int" [x]

lspOp (Cast IntegerType IntType) [x] = x
lspOp (Cast DoubleType IntType) [x] = op "floor" [x]
lspOp (Cast StringType IntType) [x] = op "cast-string-int" [x]
lspOp (Cast CharType IntType) [x] = op "char->integer" [x]

lspOp (Cast IntegerType DoubleType) [x] = op "exact->inexact" [x]
lspOp (Cast IntType DoubleType) [x] = op "exact->inexact" [x]
lspOp (Cast StringType DoubleType) [x] = op "cast-string-double" [x]

lspOp (Cast IntType CharType) [x] = op "integer->char" [x]

lspOp (Cast from to) [x] = "(blodwen-error-quit \"Invalid cast " ++ show from ++ "->" ++ show to ++ "\")"

lspOp BelieveMe [_,_,x] = x

||| Extended primitives for the lisp backend, outside the standard set of primFn
public export
data ExtPrim = CCall | LispCall | PutStr | GetStr
             | FileOpen | FileClose | FileReadLine | FileWriteLine | FileEOF
             | NewIORef | ReadIORef | WriteIORef
             | Stdin | Stdout | Stderr
             | VoidElim | Unknown Name

export
Show ExtPrim where
  show CCall = "CCall"
  show LispCall = "LispCall"
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
  show Stdin = "Stdin"
  show Stdout = "Stdout"
  show Stderr = "Stderr"
  show VoidElim = "VoidElim"
  show (Unknown n) = "Unknown " ++ show n

||| Match on a user given name to get the lisp primitive
toPrim : Name -> ExtPrim
toPrim pn@(NS _ n)
    = cond [(n == UN "prim__lispCall", LispCall),
            (n == UN "prim__cCall", CCall),
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
            (n == UN "prim__stdin", Stdin),
            (n == UN "prim__stdout", Stdout),
            (n == UN "prim__stderr", Stderr),
            (n == UN "void", VoidElim)
            ]
           (Unknown pn)
toPrim pn = Unknown pn

export
mkWorld : String -> String
mkWorld res = lspConstructor 0 ["#f", res, "#f"] -- MkIORes

lspConstant : Constant -> String
lspConstant (I x) = show x
lspConstant (BI x) = show x
lspConstant (Str x) = show x
lspConstant (Ch x) = "#\\" ++ cast x
lspConstant (Db x) = show x
lspConstant WorldVal = "#f"
lspConstant IntType = "#t"
lspConstant IntegerType = "#t"
lspConstant StringType = "#t"
lspConstant CharType = "#t"
lspConstant DoubleType = "#t"
lspConstant WorldType = "#t"

lspCaseDef : Maybe String -> String
lspCaseDef Nothing = ""
lspCaseDef (Just tm) = "(else " ++ tm ++ ")"

parameters (lspExtPrim : {vars : _} -> Int -> SVars vars -> ExtPrim -> List (CExp vars) -> Core String)
  mutual
    lspConAlt : Int -> SVars vars -> String -> CConAlt vars -> Core String
    lspConAlt {vars} i vs target (MkConAlt n tag args sc)
        = let vs' = extendSVars args vs in
              pure $ "((" ++ show tag ++ ") "
                          ++ bindArgs 1 args vs' !(lspExp i vs' sc) ++ ")"
      where
        bindArgs : Int -> (ns : List Name) -> SVars (ns ++ vars) -> String -> String
        bindArgs i [] vs body = body
        bindArgs i (n :: ns) (v :: vs) body
            = "(let ((" ++ v ++ " " ++ "(vector-ref " ++ target ++ " " ++ show i ++ "))) "
                    ++ bindArgs (i + 1) ns vs body ++ ")"

    lspConstAlt : Int -> SVars vars -> String -> CConstAlt vars -> Core String
    lspConstAlt i vs target (MkConstAlt c exp)
        = pure $ "((equal? " ++ target ++ " " ++ lspConstant c ++ ") " ++ !(lspExp i vs exp) ++ ")"

    -- oops, no traverse for Vect in Core
    lspArgs : Int -> SVars vars -> Vect n (CExp vars) -> Core (Vect n String)
    lspArgs i vs [] = pure []
    lspArgs i vs (arg :: args) = pure $ !(lspExp i vs arg) :: !(lspArgs i vs args)

    export
    lspExp : Int -> SVars vars -> CExp vars -> Core String
    lspExp i vs (CLocal fc el) = pure $ lookupSVar el vs
    lspExp i vs (CRef fc n) = pure $ lspName n
    lspExp i vs (CLam fc x sc)
       = do let vs' = extendSVars [x] vs
            sc' <- lspExp i vs' sc
            pure $ "(lambda (" ++ lookupSVar First vs' ++ ") " ++ sc' ++ ")"
    lspExp i vs (CLet fc x val sc)
       = do let vs' = extendSVars [x] vs
            val' <- lspExp i vs val
            sc' <- lspExp i vs' sc
            pure $ "(let ((" ++ lookupSVar First vs' ++ " " ++ val' ++ ")) " ++ sc' ++ ")"
    lspExp i vs (CApp fc x [])
        = pure $ "(" ++ !(lspExp i vs x) ++ ")"
    lspExp i vs (CApp fc x args)
        = pure $ "(" ++ !(lspExp i vs x) ++ " " ++ showSep " " !(traverse (lspExp i vs) args) ++ ")"
    lspExp i vs (CCon fc x tag args)
        = pure $ lspConstructor tag !(traverse (lspExp i vs) args)
    lspExp i vs (COp fc op args)
        = pure $ lspOp op !(lspArgs i vs args)
    lspExp i vs (CExtPrim fc p args)
        = lspExtPrim i vs (toPrim p) args
    lspExp i vs (CForce fc t) = pure $ "(force " ++ !(lspExp i vs t) ++ ")"
    lspExp i vs (CDelay fc t) = pure $ "(delay " ++ !(lspExp i vs t) ++ ")"
    lspExp i vs (CConCase fc sc alts def)
        = do tcode <- lspExp (i+1) vs sc
             defc <- maybe (pure Nothing) (\v => pure (Just !(lspExp i vs v))) def
             let n = "sc" ++ show i
             pure $ "(let ((" ++ n ++ " " ++ tcode ++ ")) (case (get-tag " ++ n ++ ") "
                     ++ showSep " " !(traverse (lspConAlt (i+1) vs n) alts)
                     ++ lspCaseDef defc ++ "))"
    lspExp i vs (CConstCase fc sc alts def)
        = do defc <- maybe (pure Nothing) (\v => pure (Just !(lspExp i vs v))) def
             tcode <- lspExp (i+1) vs sc
             let n = "sc" ++ show i
             pure $ "(let ((" ++ n ++ " " ++ tcode ++ ")) (cond "
                      ++ showSep " " !(traverse (lspConstAlt (i+1) vs n) alts)
                      ++ lspCaseDef defc ++ "))"
    lspExp i vs (CPrimVal fc c) = pure $ lspConstant c
    lspExp i vs (CErased fc) = pure "'()"
    lspExp i vs (CCrash fc msg) = pure $ "(blodwen-error-quit " ++ show msg ++ ")"

  -- Need to convert the argument (a list of lisp arguments that may
  -- have been constructed at run time) to a lisp list to be passed to apply
  readArgs : Int -> SVars vars -> CExp vars -> Core String
  readArgs i vs tm = pure $ "(blodwen-read-args " ++ !(lspExp i vs tm) ++ ")"

  fileOp : String -> String
  fileOp op = "(blodwen-file-op (lambda () " ++ op ++ "))"

  -- External primitives which are common to the lisp codegens (they can be
  -- overridden)
  export
  lspExtCommon : Int -> SVars vars -> ExtPrim -> List (CExp vars) -> Core String
  lspExtCommon i vs LispCall [ret, CPrimVal fc (Str fn), args, world]
     = pure $ mkWorld ("(apply " ++ fn ++" "
                  ++ !(readArgs i vs args) ++ ")")
  lspExtCommon i vs LispCall [ret, fn, args, world]
       = pure $ mkWorld ("(apply (eval (string->symbol " ++ !(lspExp i vs fn) ++")) "
                    ++ !(readArgs i vs args) ++ ")")
  lspExtCommon i vs PutStr [arg, world]
      = pure $ "(display " ++ !(lspExp i vs arg) ++ ") " ++ mkWorld (lspConstructor 0 []) -- code for MkUnit
  lspExtCommon i vs GetStr [world]
      = pure $ mkWorld "(blodwen-get-line (current-input-port))"
  lspExtCommon i vs FileOpen [file, mode, bin, world]
      = pure $ mkWorld $ fileOp $ "(blodwen-open "
                                      ++ !(lspExp i vs file) ++ " "
                                      ++ !(lspExp i vs mode) ++ " "
                                      ++ !(lspExp i vs bin) ++ ")"
  lspExtCommon i vs FileClose [file, world]
      = pure $ "(blodwen-close-port " ++ !(lspExp i vs file) ++ ") " ++ mkWorld (lspConstructor 0 [])
  lspExtCommon i vs FileReadLine [file, world]
      = pure $ mkWorld $ fileOp $ "(blodwen-get-line " ++ !(lspExp i vs file) ++ ")"
  lspExtCommon i vs FileWriteLine [file, str, world]
      = pure $ mkWorld $ fileOp $ "(blodwen-putstring "
                                        ++ !(lspExp i vs file) ++ " "
                                        ++ !(lspExp i vs str) ++ ")"
  lspExtCommon i vs FileEOF [file, world]
      = pure $ mkWorld $ "(blodwen-eof " ++ !(lspExp i vs file) ++ ")"
  lspExtCommon i vs NewIORef [_, val, world]
      = pure $ mkWorld $ "(box " ++ !(lspExp i vs val) ++ ")"
  lspExtCommon i vs ReadIORef [_, ref, world]
      = pure $ mkWorld $ "(unbox " ++ !(lspExp i vs ref) ++ ")"
  lspExtCommon i vs WriteIORef [_, ref, val, world]
      = pure $ mkWorld $ "(set-box! "
                           ++ !(lspExp i vs ref) ++ " "
                           ++ !(lspExp i vs val) ++ ")"
  lspExtCommon i vs VoidElim [_, _]
      = pure "(display \"Error: Executed 'void'\")"
  lspExtCommon i vs (Unknown n) args
      = throw (InternalError ("Can't compile unknown external primitive " ++ show n))
  lspExtCommon i vs Stdin [] = pure "(current-input-port)"
  lspExtCommon i vs Stdout [] = pure "(current-output-port)"
  lspExtCommon i vs Stderr [] = pure "(current-error-port)"
  lspExtCommon i vs prim args
      = throw (InternalError ("Badly formed external primitive " ++ show prim
                                ++ " " ++ show args))

  lspArglist : SVars ns -> String
  lspArglist [] = ""
  lspArglist [x] = x
  lspArglist (x :: xs) = x ++ " " ++ lspArglist xs

  lspDef : {auto c : Ref Ctxt Defs} ->
           Name -> CDef -> Core String
  lspDef n (MkFun args exp)
     = let vs = initSVars args in
           pure $ "(define " ++ lspName !(getFullName n) ++ " (lambda (" ++ lspArglist vs ++ ") "
                      ++ !(lspExp 0 vs exp) ++ "))\n"
  lspDef n (MkError exp)
     = pure $ "(define (" ++ lspName !(getFullName n) ++ " . any-args) " ++ !(lspExp 0 [] exp) ++ ")\n"
  lspDef n (MkCon t a) = pure "" -- Nothing to compile here

-- Convert the name to lisp code
-- (There may be no code generated, for example if it's a constructor)
export
getLisp : {auto c : Ref Ctxt Defs} ->
          (lspExtPrim : {vars : _} -> Int -> SVars vars -> ExtPrim -> List (CExp vars) -> Core String) ->
          Defs -> Name -> Core String
getLisp lspExtPrim defs n
    = case !(lookupCtxtExact n (gamma defs)) of
           Nothing => throw (InternalError ("Compiling undefined name " ++ show n))
           Just d => case compexpr d of
                          Nothing =>
                             throw (InternalError ("No compiled definition for " ++ show n))
                          Just d => lspDef lspExtPrim n d
