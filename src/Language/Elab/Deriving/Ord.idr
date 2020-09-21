module Language.Elab.Deriving.Ord

-- Public: Things here we actually use in deriving Eq need to be re-exported to
-- be available at the deriving use-site. A little odd but that's how it is.
-- Otherwise you get extremely vague "Can't reify as X" errors and chances are
-- you don't have an FC to track it down.

import public Language.Elab.Syntax
import public Language.Elab.Types

import public Util
import public Language.Elab.Deriving.Util

import public Language.Reflection

import Language.Elab.Deriving.Eq

%language ElabReflection


addAutoImps : List String -> Name -> TTImp -> TTImp
addAutoImps xs na retty
  = foldr (\arg,tt => `(~(iVar na) ~(iBindVar arg) => ~(tt))) retty xs

addOrdAutoImps : List String -> TTImp -> TTImp
addOrdAutoImps xs retty
  = foldr (\arg,tt => `(Ord ~(iBindVar arg) => ~(tt))) retty xs

-- I want better names here, including better index names
-- e.g we have this now
{-
Language.Elab.Deriving.Eq.eqImplFoo6'Fun : Eq arg6281 => Eq arg6282
  => Eq arg6283 => Foo6' arg6281 arg6282 arg6283 arg6284
    -> Foo6' arg6281 arg6282 arg6283 arg6284 -> Bool
-}

||| e.g. compare : Foo a b -> Foo a b -> Ordering
compareClaim : (opname : Name) -> TypeInfo -> Visibility -> Elab Decl
compareClaim op tyinfo vis = do
  let conargs = pullExplicits tyinfo
      varnames = map (show . name) conargs
      params = map (extractNameStr . name) $ filter (not . isIndex) conargs
      tysig = `(~(tyinfo.type) -> ~(tyinfo.type) -> Ordering)
  logMsg "compareClaim" 1 $ ("auto params: ") ++ show params
  -- NB: I can't think of a reason not to Inline here
  pure $ iClaim MW vis [Inline] (mkTy op (addOrdAutoImps params tysig))


compareClause : (opname : Name)
             -> (Int, (Name, List ArgInfo, TTImp))
             -> (Int, (Name, List ArgInfo, TTImp)) -> Elab Clause
compareClause op (i1,(conname1,args1,imp1)) (i2,(conname2,args2,imp2)) = do
    let vars1 = filter (isExplicitPi . piInfo) args1
    let vars2 = filter (isExplicitPi . piInfo) args2
    let pats1 = makePatNames vars1 infVars "_1"
    let pats2 = makePatNames vars2 infVars "_2"
    let lhs = iVar op `iApp` (makePat conname1 pats1) `iApp` (makePat conname2 pats2)
    let rhs = case compare i1 i2 of
                LT => `(LT)
                GT => `(GT)
                EQ => makeRhs (zip (catMaybes pats1) (catMaybes pats2))
    pure $ patClause lhs rhs
  where
    -- Make our pat names, we use Just to flag the vars we want to use, we don't
    -- compare indices since they're vacuously EQ for the Ord interface.
    -- It doesn't seem to matter if an index is M1 or not.
    makePatNames : List ArgInfo
               -> Stream String -> String -> List (Maybe Name)
    makePatNames [] vs s = []
    makePatNames (a :: as) (v :: vs) s
      = let xs = makePatNames as vs s
            basicname = UN v
        in if isUse0 a.count || a.isIndex
             then Nothing :: xs
             else Just (mapName (++ s) basicname) :: xs

    -- The lhs of our function, fields we don't want to use are replaced with _
    makePat : (con : Name) -> (vars : List (Maybe Name)) -> TTImp
    makePat con vars = foldl
      (\tt,v => `(~(tt) ~(maybe implicit' bindNameVar v))) (iVar con) vars

    -- A little wordy here, it's set up this way instead of a fold to avoid an
    -- extra True when building up our && chain. There's no reason to make the
    -- user repeat work every time they use their derived implementation.
    makeRhs : List (Name,Name) -> TTImp
    makeRhs [] = `(EQ)
    makeRhs [(x,y)] = `( compare ~(iVar x) ~(iVar y) )
    makeRhs ((x,y) :: xs) = `( compare ~(iVar x) ~(iVar y) <+> ~(makeRhs xs) )

-- Assign a number to the position of a constructor. We use this to check simple
-- ordering. When equal we go on to check constituents.
compareClauses : (opname : Name) -> TypeInfo -> Elab (List Clause)
compareClauses op tyinfo = do
    let ncons = zipSL [0..] tyinfo.cons
        clauses = [| compareClause (pure op) ncons ncons |]
    logMsg "compareClauses" 1 ""
    sequence clauses
    -- pure [] --clauses

||| The record that idris would make for you when you write an implementation.
ordObject : (decname : Name) -> (funname : Name) -> TypeInfo
          -> Visibility -> Elab (Decl, Decl)
ordObject decname eqfun tyinfo vis = do
  (qname,_) <- lookupName `{{Ord}}
  [NS _ (DN _ ordcon)] <- getCons qname
    | _ => fail "ordObject: error during Ord constructor lookup"
  (qname',tyimp) <- lookupName ordcon
  let conargs' = pullExplicits tyinfo
  logMsg "sada" 1 $ show (length conargs')
  logTerm "lll" 1 "" tyimp
  let conargs = pullExplicits tyinfo
      varnames = map (show . name) conargs
      varnames' = map (show . name) (filter (not . isIndex) conargs)
      ty = appTyCon (map (show . name) conargs)  tyinfo.name
      retty = `( Ord ~(appTyCon (map (show . name) conargs)  tyinfo.name))
      tysig = `( Eq ~ty => ~(addOrdAutoImps varnames' retty))
  logTerm "ty" 1 "asd" ty
  let
      claim = iClaim MW vis [Hint True] (mkTy decname tysig)
      compare = iVar eqfun
      lt = `(\x,y => compare x y == LT)
      gt = `(\x,y => compare x y == GT)
      lte = `(\x,y => compare x y /= GT)
      gte = `(\x,y => compare x y /= LT)
      max = `(\x,y => case compare x y of LT => y; _ => x)
      min = `(\x,y => case compare x y of LT => x; _ => y)
      -- neqfun = `(\x,y => not (x == y))
      -- neqfun = `(\x,y => not (x == y))
      -- neqfun = `(\x,y => not (x == y))
      rhs = `( ~(iVar ordcon) %search ~compare ~lt ~gt ~lte ~gte ~max ~min)
      body = iDef decname [(patClause (iVar decname) rhs)]
  logDecls 1 "claim" [claim]
  logDecls 1 "body" [body]

  pure $ (claim,body)

-- 
-- (%pi Rig0 Implicit (Just ty)
--   %type
--   (%pi Rig1 Explicit (Just {arg:368})
--     (Prelude.EqOrd.Eq ty)
--     (%pi RigW Explicit (Just compare)
--       (%pi RigW Explicit (Just {arg:369})
--         ty
--         (%pi RigW Explicit (Just {arg:370})
--           ty Prelude.EqOrd.Ordering))
--       (%pi RigW Explicit (Just <)
--         (%pi RigW Explicit (Just {arg:371})
--           ty
--           (%pi RigW Explicit (Just {arg:372})
--             ty
--             Prelude.Basics.Bool))
--         (%pi RigW Explicit (Just >)
--           (%pi RigW Explicit (Just {arg:373})
--             ty
--             (%pi RigW Explicit (Just {arg:374})
--               ty
--               Prelude.Basics.Bool))
--           (%pi RigW Explicit (Just <=)
--             (%pi RigW Explicit (Just {arg:375})
--               ty
--               (%pi RigW Explicit (Just {arg:376})
--                 ty
--                 Prelude.Basics.Bool))
--             (%pi RigW Explicit (Just >=)
--               (%pi RigW Explicit (Just {arg:377})
--                 ty
--                 (%pi RigW Explicit (Just {arg:378})
--                   ty
--                   Prelude.Basics.Bool))
--               (%pi RigW Explicit (Just max)
--                 (%pi RigW Explicit (Just {arg:379})
--                   ty
--                   (%pi RigW Explicit (Just {arg:380})
--                     ty
--                     ty))
--                 (%pi RigW Explicit (Just min)
--                   (%pi RigW Explicit (Just {arg:381})
--                     ty
--                     (%pi RigW Explicit (Just {arg:382})
--                       ty
--                       ty))
--                   (Prelude.EqOrd.Ord ty))))))))))



export
||| Usage: %runElab deriveEq Export `{{Foo}}
||| Currently, this adds eqImplFoo and eqImpltFooFun to the module namespace.
||| This is likely to change in the future to only have eqImplFoo being added
||| to the namespace.
deriveOrd : Visibility -> Name -> Elab ()
deriveOrd vis dataname = do
    (qname,_) <- lookupName dataname -- get the qualified name of our type
    -- create human readable names for our instance components
    let decn = mapName (\d => "ordImpl" ++ d) dataname
        funn = mapName (\d => "ordImpl" ++ d ++ "Fun") dataname
    -- Build general info about the type we're deriving (e.g. Foo) that we want
    -- to keep around.
    tyinfo <- makeTypeInfo qname

    -- The components of our eq-ing function
    funclaim <- compareClaim funn tyinfo Private -- NB private
    funclauses <- compareClauses funn tyinfo

    -- Our function's complete definition
    let fundecl = iDef funn funclauses

    -- The actual eqImplFoo : Eq Foo record.
    (objclaim,objclause) <- ordObject decn funn tyinfo vis

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

-- NB c is never used, so Eq shouldn't be required for it
data Foo7 : Type -> Type -> Type -> Type where
  Zor7 : a -> Foo7 a b c
  Gor7 : b -> Foo7 a b c
  Nor7A : a -> b -> Foo7 a b c
  Nor7B : a -> b -> c -> Foo7 a b c
  Bor7 : Foo7 a b c

-- NB a is never used, so Eq shouldn't be required for it
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
  Pah6'  : a -> (n : MyNat) -> MyNat -> (0 _ : c) -> Foo6' a b c n
  -- Rah6'  : a -> (n : MyNat) -> Foo6' a b c n -> MyNat -> (0 _ : c) -> Foo6' a b c n -> Foo6' a b c n
  -- Gah6'  : {1 _ : a} -> (n : MyNat) -> MyNat -> (0 _ : c) -> Foo6' a b c n
  -- ^ another case to consider, what if I'm implicit but M1?
  -- Seems like an error would be appropriate there rather than showing
  -- implicits. Though showing implicits could be a flag in instance generation
  -- I guess.

-- eqImplFoo6'Fun (Wah6' 'c' MZ) (Wah6' 'c' MZ)
-- eqImplFoo6'Fun (Nor6A' {n=MZ} 'c' 'd' 'e')

-- eqImplFoo6Fun (Wah6 {b=Int} {c=String} 'c' (S Z)) (Wah6 'c' (S Z))

-- reference impl
-- NB We need to use n twice, Eq is not dependent, two values of `a` compared
-- against each other must have the same indices. Which follows since if they
-- don't they're obviously not equal.
-- if a con has no explicit, non-M0, non-index, vars then it's empty, and thus
-- vauously true to compare to itself. only explicit, non-M0, non-index vars need
-- to be compared. M0 values can't be used and index vars can't vary in an Eq
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

%runElab deriveEq Export `{{MyNat}}
%runElab deriveOrd Export `{{MyNat}}
%runElab deriveOrd Export `{{Foo1}}
%runElab deriveEq Export  `{{Foo2}}
%runElab deriveOrd Export `{{Foo2}} -- works but doesn't warn if no Eq instance
%runElab deriveOrd Private `{{Foo4}}
%runElab deriveOrd Private `{{Foo5}}
%runElab deriveOrd Private `{{Foo7}}
%runElab deriveOrd Private `{{Foo7'}}
-- %runElab deriveOrd Private `{{FooN}} -- trouble with indices still
-- %runElab deriveOrd Private `{{Foo6}}
-- %runElab deriveOrd Export  `{{Foo6'}}

