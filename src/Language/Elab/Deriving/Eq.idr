module Language.Elab.Deriving.Eq

import Language.Elab.Syntax
import Language.Elab.Types

import Util
import Language.Elab.Deriving.Util

import Language.Reflection
import Data.Strings -- fastAppend



-- A regular isntance might look like (Eq a, Eq b, Eq c) => ...
-- This pairing isn't actually neccesary, it's just notational convenience and
-- we don't really have a reason to emulate it.
-- Eq a => Eq b => ...  is just as valid as (Eq a, Eq b) => ...
-- It also can result in clearer errors.
addEqAutoImps : List String -> TTImp -> TTImp
addEqAutoImps xs retty
  = foldr (\arg,tt => `(Eq ~(iBindVar arg) => ~(tt))) retty xs

-- I want better names here, including better index names
-- e.g we have this now
{-
Language.Elab.Deriving.Eq.eqImplFoo6'Fun : Eq arg6281 => Eq arg6282
  => Eq arg6283 => Foo6' arg6281 arg6282 arg6283 arg6284
    -> Foo6' arg6281 arg6282 arg6283 arg6284 -> Bool
-}

||| e.g. (==) : Foo a b -> Foo a b -> Bool
eqClaim : (opname : Name) -> TypeInfo -> Visibility -> Elab Decl
eqClaim op tyinfo vis = do
  let conargs = pullExplicits tyinfo
      varnames = map (show . name) conargs
      params = map (extractNameStr . name) $ filter (not . isIndex) conargs
      tysig = `(~(tyinfo.type) -> ~(tyinfo.type) -> Bool)
  logMsg 1 $ ("auto params: ") ++ show params
  -- NB: I can't think of a reason not to Inline here
  pure $ iClaim MW vis [Inline] (mkTy op (addEqAutoImps params tysig))

eqCon : (opname : Name) -> (Name, List ArgInfo, TTImp) -> Elab Clause
eqCon op (conname, args, contype) = do
    let vars = filter (isExplicitPi . piInfo) args
        (pats1, pats2) = makePatNames vars infVars
        lhs = iVar op `iApp` makePat conname pats1 `iApp` makePat conname pats2
        rhs = makeRhs (zip (catMaybes pats1) (catMaybes pats2))
        rhs2 = `(True)
    pure $ patClause lhs rhs
  where
    -- Make our pat names, we use Just to flag the vars we want to use, we don't
    -- compare indices since they're vacuously the same for the Eq interface.
    -- It doesn't seem to matter if an index is M1 or not.
    makePatNames : List ArgInfo
               -> Stream String -> (List (Maybe Name), List (Maybe Name))
    makePatNames [] vs = ([],[])
    makePatNames (a :: as) (v :: vs)
      = let (xs,ys) = makePatNames as vs
            basicname = UN v
        in if isUse0 a.count || a.isIndex
             then (Nothing :: xs, Nothing :: ys)
             else (Just (mapName (++ "_1") basicname) :: xs
                  ,Just (mapName (++ "_2") basicname) :: ys)

    -- The lhs of our function, fields we don't want to use are replaced with _
    makePat : (con : Name) -> (vars : List (Maybe Name)) -> TTImp
    makePat con vars = foldl
      (\tt,v => `(~(tt) ~(maybe implicit' bindNameVar v))) (iVar con) vars

    -- A little wordy here, it's set up this way instead of a fold to avoid an
    -- extra True when building up our && chain. There's no reason to make the
    -- user repeat work every time they use their derived implementation.
    makeRhs : List (Name,Name) -> TTImp
    makeRhs [] = `(True)
    makeRhs [(x,y)] = `( ~(iVar x) == ~(iVar y) )
    makeRhs ((x,y) :: xs) = `( ~(iVar x) == ~(iVar y) && ~(makeRhs xs) )


||| The record that idris would make for you when you write an implementation.
eqObject : (decname : Name) -> (funname : Name) -> TypeInfo
          -> Visibility -> Elab (Decl, Decl)
eqObject decname eqfun tyinfo vis = do
  (qname,_) <- lookupName `{{Eq}}
  [NS _ (DN _ eqcon)] <- getCons qname
    | _ => fail "eqObject: error during Eq constructor lookup"
  let conargs = pullExplicits tyinfo
      varnames = map (show . name) conargs
      varnames' = map (show . name) (filter (not . isIndex) conargs)
      retty = `( Eq ~(appTyCon (map (show . name) conargs)  tyinfo.name))
      tysig = addEqAutoImps varnames' retty
      claim = iClaim MW vis [Hint True] (mkTy decname tysig)
      neqfun = `(\x,y => not (x == y))
      rhs = `( ~(iVar eqcon) ~(iVar eqfun) ~(neqfun))
      body = iDef decname [(patClause (iVar decname) rhs)]
  pure $ (claim,body)


export
||| Usage: %runElab deriveEq Export `{{Foo}}
||| Currently, this adds eqImplFoo and eqImpltFooFun to the module namespace.
||| This is likely to change in the future to only have eqImplFoo being added
||| to the namespace.
deriveEq : Visibility -> Name -> Elab ()
deriveEq vis eqname = do
    (qname,_) <- lookupName eqname -- get the qualified name of our type
    -- create human readable names for our instance components
    let decn = mapName (\d => "eqImpl" ++ d) eqname
        funn = mapName (\d => "eqImpl" ++ d ++ "Fun") eqname
    -- Build general info about the type we're deriving (e.g. Foo) that we want
    -- to keep around.
    tyinfo <- makeTypeInfo qname
    
    -- The components of our eq-ing function
    funclaim <- eqClaim funn tyinfo Private -- NB private
    funclauses <- traverseE (eqCon funn) tyinfo.cons
    
    -- Our function's complete definition
    let catchall = patClause
          `(~(iVar funn) ~(implicit') ~(implicit'))
          `(False)
        fundecl = IDef EmptyFC funn (funclauses ++ [catchall])
    
    -- The actual eqImplFoo : Eq Foo record.
    (objclaim,objclause) <- eqObject decn funn tyinfo vis
    -- Declare our things into the namespace
    -- Both claims first, otherwise we won't find our own Eq in fundecl
    declare [funclaim, objclaim]
    declare [fundecl, objclause]




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

  -- we'll use our own nat for index experimentation
export
data MyNat : Type where
  MZ : MyNat
  MS : MyNat -> MyNat
 
-- Eq MyNat where
--   MZ == MZ = True
--   (MS x) == (MS y) = x == y
--   _ == _ = False

data Foo6 : Type -> Type -> Type -> Nat -> Type where
  Zor6 : a -> b -> Foo6 a b c Z
  Gor6 : b -> Foo6 a b c (S k)
  Nor6A : a -> b -> c -> Foo6 a b c n
  Nor6B : a -> (0 _ : b) -> c -> Foo6 a b c n -- NB: 0 Use arg
  Bor6A : Foo6 a b c n
  Bor6B : Foo6 a b c n -> Foo6 a b c n
  Wah6 : a -> (n : Nat) -> Foo6 a b c n

export
data Foo6' : Type -> Type -> Type -> MyNat -> Type where
  Zor6'  : a -> b -> Foo6' a b c MZ
  Gor6A'  : b -> Foo6' a b c (MS k)
  Gor6B'  : (k : MyNat) -> b -> Foo6' a b c (MS k)
  Nor6A' : a -> b -> c -> Foo6' a b c n
  Nor6B' : a -> (0 _ : b) -> c -> Foo6' a b c n
  Bor6'  : Foo6' a b c n
  Wah6'  : a -> (n : MyNat) -> Foo6' a b c n
  Kah6'  : a -> (n : MyNat) -> (0 _ : c) -> Foo6' a b c n
  Pah6'  : a -> (1 n : MyNat) -> MyNat -> (0 _ : c) -> Foo6' a b c n
  Pah6''  : a -> (n : MyNat) -> MyNat -> (0 _ : c) -> Foo6' a b c n
  Pah6'''  : (n : MyNat) -> (0 _ : MyNat) -> (0 _ : c) -> Foo6' a b c n
  -- Rah6'  : a -> (n : MyNat) -> Foo6' a b c n -> MyNat -> (0 _ : c) -> Foo6' a b c n -> Foo6' a b c n
  -- Gah6'  : {1 _ : a} -> (n : MyNat) -> MyNat -> (0 _ : c) -> Foo6' a b c n
  -- ^ another case to consider, what if I'm implicit but M1?
  -- Seems like an error would be appropriate there rather than showing
  -- implicits. Though showing implicits could be a flag in instance generation
  -- I guess.
-- Pah6' {b=Int} 'a' MZ MZ 'd'
eqFop : Foo6' a b c MZ -> Foo6' a b c MZ -> Bool
eqFop (Pah6' x MZ z a) (Pah6' x2 _ z2 a2) = ?dfsdf --True
eqFop _ _ = False

-- eqImplFoo6'Fun (Wah6' 'c' MZ) (Wah6' 'c' MZ)
-- eqImplFoo6'Fun (Nor6A' {n=MZ} 'c' 'd' 'e')

-- eqImplFoo6Fun (Wah6 {b=Int} {c=String} 'c' (S Z)) (Wah6 'c' (S Z))

-- reference impl
-- NB We need to use n twice, Eq is not dependent, two values of `a` compared
-- against each other must have the same indices. Which follows since if they
-- don't they're obviously not equal.
-- if a con has no explicit, non-0, non-index, vars then it's empty, and thus
-- vauously true to compare to itself. only explicit, non-0, non-index vars need
-- to be compared. 0 values can't be used and index vars can't vary in an Eq
-- definition
eqFoo6 : (Eq a, Eq b, Eq c) => Foo6 a b c n -> Foo6 a b c n -> Bool
eqFoo6 (Zor6 x1 y1) (Zor6 x2 y2) = x1 == x2 && y1 == y2
eqFoo6 (Gor6 x1) (Gor6 x2) = x1 == x2
eqFoo6 (Nor6A x1 y1 z1) (Nor6A x2 y2 z2) = x1 == x2 && y1 == y2 && z1 == z2
eqFoo6 (Nor6B x1 _ z1) (Nor6B x2 _ z2) = x1 == x2 && z1 == z2
eqFoo6 Bor6A Bor6A = True
eqFoo6 (Bor6B x1) (Bor6B x2) = eqFoo6 x1 x2
-- we prefer to write this as x1 == x2, and we do so by declaring our Eq object
-- early, otherwise there's no instance for Foo6 to use == from
eqFoo6 (Wah6 x1 _) (Wah6 x2 _) = x1 == x2 -- indices do not differ
eqFoo6 _ _ = False
-- eqFoo6 {b=Int} {c=String} (Wah6 'c' (S Z)) (Wah6 'c' (S Z))

data FooN : MyNat -> Type -> Type where
  BorZ : b -> FooN MZ b
  BorS : b -> FooN (MS MZ) b
  BorNA : (k : MyNat) -> b -> FooN n b
  BorNB : (n : MyNat) -> b -> FooN n b

%runElab deriveEq Export  `{{MyNat}}
%runElab deriveEq Export  `{{Foo1}}
%runElab deriveEq Export  `{{Foo2}}
%runElab deriveEq Private `{{Foo4}}
%runElab deriveEq Private `{{Foo5}}
%runElab deriveEq Private `{{Foo7}}
%runElab deriveEq Private `{{Foo7'}}
%runElab deriveEq Private `{{FooN}}
%runElab deriveEq Private `{{Foo6}}
%runElab deriveEq Export  `{{Foo6'}}
