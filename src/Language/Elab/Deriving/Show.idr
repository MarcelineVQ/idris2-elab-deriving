module Language.Elab.Deriving.Show

import Language.Elab.Syntax
import Language.Reflection

import Language.Elab.Types

import Util

import Data.Strings -- fastAppend

-- NB uses of things like show in the repl can cause ambiguity issues, confirm
-- this is a problem before submitting a complaint. Refer to the note at
-- bottom of this file.

intercalate_str : String -> List String -> String
intercalate_str sep ss = fastAppend (intersperse sep ss)

-- A regular isntance might look like (Show a, Show b, Show c) => ...
-- This pairing isn't actually neccesary, it's just notational convenience and
-- we don't really have a reason to emulate it.
-- Show a => Show b => ...  is just as valid as (Show a, Show b) => ...
-- It also can result in clearer errors.
addShowAutoImps : List String -> TTImp -> TTImp
addShowAutoImps xs retty
  = foldr (\arg,tt => `(Show ~(iBindVar arg) => ~(tt))) retty xs

-- It works! We still need to prune requiring Show on tvars that aren't
-- actually used, since otherwise users have to provide it.
showClaim : (opname : Name) -> TypeInfo -> Visibility -> Elab Decl
showClaim op tyinfo vis = do
  let conargs = pullExplicits tyinfo
      varnames = map (show . name) conargs
      varnames' = map (show . name) (filter (isType . type) conargs)
      tysig = `(~(appTyCon (map (show . name) conargs) tyinfo.name) -> String)
  -- NB: I can't think of a reason not to Inline here
  pure $ iClaim MW vis [Inline] (mkTy op (addShowAutoImps varnames' tysig))

showCon : (opname : Name) -> (Name, List ArgInfo, TTImp) -> Elab Clause
showCon op (conname, args, contype) = do
    let varnames = filter (isExplicitPi . piInfo) args
        lhsvars = map (show . name) varnames
        rhsvars = map (\arg => if isUse0 (count arg)
                             then Nothing
                             else Just (show arg.name)) varnames
        lhs = iVar op `iApp`
                foldl (\tt,v => `(~(tt) ~(iBindVar v))) (iVar conname) lhsvars
        rhs = foldl (\tt,v => `( ~(tt) ++ " " ++ ~(beShown v)))
                (iPrimVal (Str !(showName conname))) rhsvars
    pure $ patClause lhs rhs
  where
    beShown : Maybe String -> TTImp
    beShown (Just x) = `(show ~(iVar (UN x)))
    beShown Nothing = `("_0") -- param is 0 use


-- TOTO, really we should be defining showPrec and not show at all
-- but let's get everything else sorted out first so we're not fighting
-- type sigs. refer to: Show (Maybe a)
-- TODO if our cons are Nil and :: should we be displaying like [a,b,c] ?
-- I think so, especially since we could write the value that way
-- TODO we should be defining showPrec for things like MyNat to be right
-- currently MS (MS (MS MZ)) = "MS MS MS MZ"
showObject : (decname : Name) -> (funname : Name) -> TypeInfo
          -> Visibility -> Elab (Decl, Decl)
showObject decname showfun tyinfo vis = do
  (qname,_) <- lookupName `{{Show}}
  [NS _ (DN _ showcon)] <- getCons qname
    | _ => fail "showObject: error during Show constructor lookup"
  let conargs = pullExplicits tyinfo
      varnames = map (show . name) conargs
      varnames' = map (show . name) (filter (isType . type) conargs)
      retty = `( Show ~(appTyCon (map (show . name) conargs)  tyinfo.name))
      tysig = addShowAutoImps varnames' retty
      claim = iClaim MW vis [Hint True] (mkTy decname tysig)
       -- TODO prec ignored for the moment, we will want this
      showprecfun = `(\_,x => ~(iVar showfun) x)
      rhs = `( ~(iVar showcon) ~(iVar showfun) ~(showprecfun))
      body = iDef decname [(patClause (iVar decname) rhs)]
  pure $ (claim,body)

-- TODO determine which tyvars are actually used later. We don't need to
-- require Show for phantom parameters.
deriveShow : Visibility -> Name -> Elab ()
deriveShow vis sname = do
  
    (qname,_) <- lookupName sname -- get the qualified name of our type
    -- create human readable names for our instance components
    let decn = mapName (\d => "showImpl" ++ d) sname
        funn = mapName (\d => "showImpl" ++ d ++ "Fun") sname
    -- Build general info about the type we're deriving (e.g. Foo) that we want
    -- to keep around.
    tyinfo <- makeTypeInfo qname
    
    -- Our components for our showing function
    funclaim <- showClaim funn tyinfo Private -- NB private
    funclauses <- traverseE (showCon funn) tyinfo.cons
    
    -- Our function's complete definition
    let fundecl = IDef EmptyFC funn (funclauses)
    
    -- TODO check if an instance exists already and abort if so
    
    -- The actual showFoo : Show Foo instance.
    (objclaim,objclause) <- showObject decn funn tyinfo vis
    -- Place our things into the namespace
    -- Both claims first, otherwise we won't be able to find our own Show
    declare [funclaim, objclaim]
    declare [fundecl, objclause]

-----------------------------
-- Testing
-----------------------------

%language ElabReflection -- you can remove this once %runElab is no longer used in this module
-- That time will be when deriveShow prunes extraneous Show constraints and the
-- testing types are moved to their own module

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

-- NB c is never used, so Show shouldn't be required for it
data Foo7 : Type -> Type -> Type -> Type where
  Zor7 : a -> Foo7 a b c
  Gor7 : b -> Foo7 a b c
  Nor7A : a -> b -> Foo7 a b c
  Nor7B : a -> b -> c -> Foo7 a b c
  Bor7 : Foo7 a b c

-- NB a is never used, so Show shouldn't be required for it
data Foo7' : Type -> Type -> Type -> Type where
  Zor7' : c -> Foo7' a b c
  Gor7' : b -> Foo7' a b c
  Nor7' : b -> c -> Foo7' a b c
  Bor7' : Foo7' a b c

export
data MyNat : Type where
  MZ : MyNat
  MS : MyNat -> MyNat
-- we'll use our own nat for index experimentation

%runElab deriveShow Private `{{MyNat}}

data Foo6 : Type -> Type -> Type -> Nat -> Type where
  Zor6 : a -> b -> Foo6 a b c Z
  Gor6 : b -> Foo6 a b c (S k)
  Nor6A : a -> b -> c -> Foo6 a b c n
  Nor6B : a -> (0 _ : b) -> c -> Foo6 a b c n -- NB: 0 Use arg
  Bor6 : Foo6 a b c n
  Wah6 : a -> (n : Nat) -> Foo6 a b c n

export
data Foo6' : Type -> Type -> Type -> MyNat -> Type where
  Zor6'  : a -> b -> Foo6' a b c MZ
  Gor6'  : b -> Foo6' a b c (MS k)
  Nor6A' : a -> b -> c -> Foo6' a b c n
  Nor6B' : a -> (0 _ : b) -> c -> Foo6' a b c n
  Bor6'  : Foo6' a b c n
  Wah6'  : a -> (n : MyNat) -> Foo6' a b c n

-- reference impl
showFoo6 : (Show a, Show b, Show c) => Foo6 a b c n -> String
showFoo6 (Zor6 x y) = "Zor6" ++ " " ++ show x ++ " " ++ show y
showFoo6 (Gor6 x) = "Gor6" ++ " " ++ show x
showFoo6 (Nor6A x y z)
  = "Nor6A" ++ " " ++ show x ++ " " ++ show y ++ " " ++ show z
showFoo6 (Nor6B x _ z)
  = "Nor6B" ++ " " ++ show x ++ " " ++ "_0" ++ " " ++ show z
showFoo6 (Bor6) = "Bor6"
showFoo6 (Wah6 x i) = "Wah6" ++ " " ++ show x ++ " " ++ show i
-- showFoo6 {b=Int} {c=String} (Wah6 'c' (S Z))

data FooN : Nat -> Type -> Type where
  BorZ : b -> FooN Z b
  BorS : b -> FooN (S Z) b
  BorN : b -> FooN n b
-- show (BorN 'c')

%runElab deriveShow Export  `{{Foo1}}
%runElab deriveShow Export  `{{Foo2}}
%runElab deriveShow Private `{{Foo4}}
%runElab deriveShow Private `{{Foo5}}
%runElab deriveShow Private `{{Foo6}}
%runElab deriveShow Export  `{{Foo6'}}
%runElab deriveShow Private `{{Foo7}}
%runElab deriveShow Private `{{Foo7'}}
%runElab deriveShow Private `{{FooN}}

-- There's an issue in use of `show` from the repl as it's not going to do a
-- bunch of defaulting for you.

-- Demonstrating the problem in interface type inferring:
data Bep : Nat -> Type where
  Ish : Bep n

implementation Show (Bep n) where
  show Ish = "foo"

bif : Bep n -> String
bif = show
-- This is fine in a repl:     bif Ish
-- This is not fine in a repl: show Ish

-- forfo : (Show a, Show b, Show c) => Foo6 a b c n -> String
-- forfo = show
-- This is fine in a repl:     forfo (Nor6A 'c' 'g' 'j')
-- This is not fine in a repl: show (Nor6A 'c' 'g' 'j')

-- I don't know why our type sig should help so much, we never even use the n

