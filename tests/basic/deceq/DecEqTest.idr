module DecEqTest

import Language.Elab.Deriving.DecEq
import Decidable.Equality

%language ElabReflection

data Flippy = Dolphin | Shark

%runElab deriveDecEq Export  `{{Flippy}}

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
  -- Nor6B : a -> (0 _ : b) -> c -> Foo6 a b c n -- NB: 0 Use arg
  Bor6A : Foo6 a b c n
  Bor6B : Foo6 a b c n -> Foo6 a b c n
  Wah6 : a -> (n : Nat) -> Foo6 a b c n

export
data Foo6' : Type -> Type -> Type -> MyNat -> Type where
  Zor6'  : a -> b -> Foo6' a b c MZ
  Gor6A'  : b -> Foo6' a b c (MS k)
  Gor6B'  : (k : MyNat) -> b -> Foo6' a b c (MS k)
  Nor6A' : a -> b -> c -> Foo6' a b c n
  -- Nor6B' : a -> (0 _ : b) -> c -> Foo6' a b c n
  Bor6'  : Foo6' a b c n
  Wah6'  : a -> (n : MyNat) -> Foo6' a b c n
  -- Kah6'  : a -> (n : MyNat) -> (0 _ : c) -> Foo6' a b c n
  -- Pah6'  : a -> (n : MyNat) -> MyNat -> (0 _ : c) -> Foo6' a b c n
  -- Rah6'  : a -> (n : MyNat) -> Foo6' a b c n -> MyNat -> (0 _ : c) -> Foo6' a b c n -> Foo6' a b c n
  -- Gah6'  : {1 _ : a} -> (n : MyNat) -> MyNat -> (0 _ : c) -> Foo6' a b c n
  -- ^ another case to consider, what if I'm implicit but M1?
  -- Seems like an error would be appropriate there rather than showing
  -- implicits. Though showing implicits could be a flag in instance generation
  -- I guess.

-- eqImplFoo6'Fun (Wah6' 'c' MZ) (Wah6' 'c' MZ)
-- eqImplFoo6'Fun (Nor6A' {n=MZ} 'c' 'd' 'e')

-- eqImplFoo6Fun (Wah6 {b=Int} {c=String} 'c' (S Z)) (Wah6 'c' (S Z))


data FooN : MyNat -> Type -> Type where
  BorZ : b -> FooN MZ b
  BorS : b -> FooN (MS MZ) b
  BorNA : (k : MyNat) -> b -> FooN n b
  BorNB : (n : MyNat) -> b -> FooN n b
  
data XXX : Type where
  MkXXX : {a : Int} -> (b : Int) -> XXX

%runElab deriveDecEq Export  `{{MyNat}}
%runElab deriveDecEq Export `{{Foo1}}
%runElab deriveDecEq Export  `{{Foo2}}
%runElab deriveDecEq Private `{{Foo4}}
%runElab deriveDecEq Private `{{Foo5}}
%runElab deriveDecEq Private `{{Foo7}}
%runElab deriveDecEq Private `{{Foo7'}}
-- %runElab deriveDecEq Private `{{FooN}}
-- %runElab deriveDecEq Private `{{Foo6}}
-- %runElab deriveDecEq Export  `{{Foo6'}}
%runElab deriveDecEq Export  `{{XXX}}

-- can check what's generated via
-- :printdef eqImplFoo7'Fun
