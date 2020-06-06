module Language.Elab.Deriving.Show

import Language.Elab.Syntax
import Language.Reflection

import Data.Strings -- intercalate

%language ElabReflection -- you can remove this once %runElab is no longer used in this module

export
record ArgInfo where
  constructor MkArgInfo
  count  : Count
  piInfo : PiInfo TTImp
  argName   : Name
  argType   : TTImp

readableGenSym : String -> Elab String
readableGenSym s = do MN n i <- genSym s
                        | _ => fail "readableGenSym failure"
                      pure (n ++ show i)

-- Fully qualified Name
-- Vect since we want to track our indices anyway
-- `type` is our fully applied type, e.g. given args a,b,c: Foo a b c
export
record TypeInfo where
  constructor MkTypeInfo
  tiName : Name
  args : List ArgInfo
  tiType : TTImp

-- makes them unique for now
export
genArgs : Name -> Elab (List ArgInfo)
genArgs qn = do (_,tyimp) <- lookupName qn
                go tyimp
  where
    go : TTImp -> Elab (List ArgInfo)
    go (IPi _ c i n argTy retTy)
      = [| pure (MkArgInfo c i !(UN <$> readableGenSym "arg") argTy) :: go retTy |]
    go _ = pure []

makeTypeInfo : Name -> Elab TypeInfo
makeTypeInfo n = do
  args <- genArgs n
  let explArgs = filter (isExplicitPi . piInfo) args
      explArgNames = map argName explArgs
      ty = foldl (\term,arg => `( ~(term) ~(iVar arg))) (iVar n) explArgNames
  pure $ MkTypeInfo n args ty

-- determine if M0 should be excluded from Explicit as well
pullExplicits : TypeInfo -> List ArgInfo
pullExplicits x = filter (isExplicitPi . piInfo) (args x)

pullImplicits : TypeInfo -> List ArgInfo
pullImplicits x = filter (isImplicitPi . piInfo) (args x)

intercalate_str : String -> List String -> String
intercalate_str sep ss = fastAppend (intersperse sep ss)

-- It works! We still need to prune requring Show on tvars that aren't
-- actually used, since otherwise users have to provide it.
showClaim : (opname : Name) -> TypeInfo -> Visibility -> Elab Decl
showClaim op tyinfo vis = do
    let varnames = map (show . argName) (pullExplicits tyinfo)
        ty = appTyCon varnames
        tysig = `( ~(ty) -> String )
        autoimps = foldr (\v,tt => `(Show ~(iBindVar v) => ~(tt))) tysig varnames
    pure $ iClaim MW vis [] (mkTy op autoimps)
  where
    appTyCon : List String -> TTImp
    appTyCon ns = foldl (\tt,v => `( ~(tt) ~(iBindVar v) )) (iVar (tiName tyinfo)) ns

showCon : (opname : Name) -> TypeInfo -> (conname : Name) -> Elab Clause
showCon op tyinfo con = do
    coninfo <- makeTypeInfo con
    conname <- conStr (tiName coninfo)
    let varnames = map (show . argName) (pullExplicits coninfo)
        lhs = iVar op `iApp` foldl (\tt,v => tt `iApp` (iBindVar v)) (iVar con) varnames
        rhs = foldl (\tt,v => `( ~(tt) ++ " " ++ show ~(iVar (UN v))))
                (iPrimVal (Str conname)) varnames
    pure $ patClause lhs rhs
  where
    conStr : Name -> Elab String
    conStr n = let s = extractNameStr n
               in  case strM s of
                     StrNil => fail "empty datacon in: showCon"
                     StrCons x xs => pure $
                       if isAlpha x then s else "(" ++ s ++ ")"


-- TODO determine which tyvars are actually used later. We don't need to require
-- Show a for phantom parameters.
-- I should really be defining a showPrec because we could need parens in
-- places. e.g. something that contains a Maybe needs to parens the Just x
deriveShow : Visibility -> Name -> Elab ()
deriveShow vis n = do
    (name,_) <- lookupName n
    fun <- pure $ mapName ("show" ++) n -- create a human readable function name
    cons <- getCons name

    tyinfo <- makeTypeInfo name
    c <- showClaim fun tyinfo vis
    
    cs <- traverse (showCon fun tyinfo) cons
    let g = IDef EmptyFC fun cs
    logDecls 1 "fefa" [c]
    logDecls 1 "fofo" [g]
    
    declare [c,g]


-----------------------------
-- Testing
-----------------------------

export
data Foo1 : Type -> Type where
  Bor1 : Foo1 a

export
data Foo2 : Type -> Type where
  Bor2 : a -> Foo2 a

data Foo4 : Type -> Type -> Type where
  Bor4 : b -> Foo4 a b

data Foo5 : Type -> Type -> Type -> Type where
  Bor5 : a -> b -> c -> Foo5 a b c

data Foo6 : Type -> Type -> Type -> Type where
  Zor6 : a -> b -> Foo6 a b c
  Gor6 : b -> Foo6 a b c
  Nor6 : a -> b -> c -> Foo6 a b c
  Bor6 : Foo6 a b c

-- NB c is never used, so Show shouldn't be required for it
data Foo7 : Type -> Type -> Type -> Type where
  Zor7 : a -> Foo7 a b c
  Gor7 : b -> Foo7 a b c
  Nor7 : a -> b -> Foo7 a b c
  Bor7 : Foo7 a b c

-- NB a is never used, so Show shouldn't be required for it
data Foo7' : Type -> Type -> Type -> Type where
  Zor7' : c -> Foo7' a b c
  Gor7' : b -> Foo7' a b c
  Nor7' : b -> c -> Foo7' a b c
  Bor7' : Foo7' a b c

forfo : Show (Foo6 a b c)
forfo = ?forfo_rhs

-- %runElab deriveShow Export `{{Foo}}
%runElab deriveShow Export `{{Foo2}}
%runElab deriveShow Private `{{Foo5}}

-- These are created fine but use of them is overly restricted currently
-- We're generating more Show ty constraints than neccsary
-- e.g. to show Foo1 we have to write: showFoo1 (Bor1 {a=Int})
-- But in reality we don't use `show` so that's silly.
%runElab deriveShow Export `{{Foo1}}
%runElab deriveShow Private `{{Foo6}}
%runElab deriveShow Private `{{Foo7}}
%runElab deriveShow Private `{{Foo7'}}



showFoo6' : (Show c, (Show b, Show a)) => Foo6 a b c -> String
showFoo6' (Zor6 x y) = "Zor6" ++ show x ++ show y
showFoo6' (Gor6 x) = "Gor6" ++ show x
showFoo6' (Nor6 x y z) = "Nor6" ++ show z
showFoo6' (Bor6) = "Bor6" 




-- 
-- smt : a
-- 
-- max : (x : Int) -> (y : Int) -> (v : Int ** (v >= x = True, v >= y = True))
-- 
-- f : Int -> Int
-- f x = fst (max x (fst (MkDPair {p = (\v => v == 0 = True)} 0 smt)))
-- 
-- 