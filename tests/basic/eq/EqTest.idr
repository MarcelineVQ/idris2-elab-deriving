module EqTest

import Data.Nat

import Language.Elab.Deriving.Eq
%language ElabReflection

-- Testing of elaborations all on their own. (At bottom.)

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

-- This should also be handled by Eq but is not currently.
-- data XXX : Type where
--   MkXXX : {a : Int} -> XXX

-- %runElab deriveEq Export `{{XXX}}

-- --returns True
-- testXXX : Bool
-- testXXX = MkXXX {a = 5} == MkXXX {a = 7}

%runElab deriveEq Export  `{{MyNat}}
%runElab deriveEq Export `{{Foo1}}
%runElab deriveEq Export  `{{Foo2}}
%runElab deriveEq Private `{{Foo4}}
%runElab deriveEq Private `{{Foo5}}
%runElab deriveEq Private `{{Foo7}}
%runElab deriveEq Private `{{Foo7'}}
%runElab deriveEq Private `{{FooN}}
%runElab deriveEq Private `{{Foo6}}
%runElab deriveEq Export  `{{Foo6'}}

-- can check what's generated via
-- :printdef eqImplFoo7'Fun
