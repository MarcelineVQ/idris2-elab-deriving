module Language.Elab.Deriving

import Language.Reflection

%language ElabReflection

-- Elaboration for == for Foo, we would like to generalize this once we can
-- query datatypes like Foo for what constructors they have. Further it's
-- important to be able to have this work on more complex types like
-- data Foo : Type -> Type where
--   Bob : a -> Foo a
-- In which case we need to be able to search for == for `a` so we can use that
-- and quit if one doesn't exist.
-- Currently this module would only be applicable to enumeration types.
-- This is an immediate concern because a lot of the reason I even want
-- reflection is to derive for newtypes.

-----------------------------

-- Elaboration for == for Foo

data Foo = Biz | Baz

{-
NB
(==) : Foo -> Foo -> Bool
(==) Biz Biz = True
(==) Baz Baz = True
(==) _ _ = False

-- == becomes basically this
(===) : Foo -> Foo -> Bool
(===) a b = case a of
             Biz => case b of
                      Biz => True
                      _   => False
             Baz => case b of
                      Baz => True
                      _   => False
-}

-- Did our constructor match
isConPat : TTImp -> Clause
isConPat con = PatClause EmptyFC con `(True)
--                          e.g. Biz => True

-- it did not
elseFalse : Clause
elseFalse = PatClause EmptyFC `(_) `(False)
--                         e.g. _ => False

-- compare the `con` we have against what `b` could be, matches or it's False
eqConClause : (lhs : TTImp) -> (rhs : TTImp) -> (rhs_ty : TTImp) -> Clause
eqConClause con b ty = PatClause EmptyFC
                      con (ICase EmptyFC b ty [isConPat con, elseFalse])
              -- e.g. Biz => case b of
              --               Biz => True
              --               _   => False

-- The body of (==)
eqDef : (ty : TTImp) -> List TTImp -> TTImp -> TTImp -> TTImp
eqDef ty cons a b = ICase EmptyFC a ty
              (map (\c => eqConClause c b ty) cons)
          -- e.g. case a of
          --        Biz => case b of
          --                 Biz => True
          --                 _   => False
          --        Baz => case b of
          --                 Baz => True
          --                 _   => False

-- Latest version of making ==, allowing your choice of type. Not sure how to
-- tidy this up just yet, if you pass around quoted things as arguments they
-- don't interact very well with reification.
-- Ideally we would query for the data constructors with some reflection
-- mechanism and just be able to write
-- (==) : Foo -> Foo -> Bool
-- (==) = elabEq
-- via some
-- elabEq : (a : ty) -> (b : ty) -> Bool
-- elabEq a b = %runElab check (eqDef `(ty) (cons ty) `(a) `(b))
-- or even simply at the top level
-- %runElab deriveEq `(Foo)
-- Though reflection for (top-level) declarations isn't in quite yet
(==) : Foo -> Foo -> Bool
(==) a b = %runElab check $ eqDef `(Foo) [`(Biz),`(Baz)] `(a) `(b)

borb1 : Biz == Baz = False
borb1 = Refl

borb2 : Biz == Biz = True
borb2 = Refl

borb3 : Baz == Baz = True
borb3 = Refl

-- If you try proofs here yourself I think idris2 doesn't do well with private
-- definitions in a namespace. This is why Zab and (==) are marked public
-- export, it's not at all really neccesary it's just a namespacing bug.
namespace Zab
  public export
  data Zab : Type where
    Zib : Zab
    Zyb : Zab
    Zob : Zab
    Zub : Zab
    Zeb : Zab
  
  --  So here's the meat, it's still a bit of a mouthful but a little better
  --  than writing == yourself
  public export
  (==) : Zab -> Zab -> Bool
  (==) a b = %runElab check
    $ eqDef `(Zab) [`(Zib),`(Zyb),`(Zob),`(Zub),`(Zeb)] `(a) `(b)

  {- -- written yourself
  (==) : Zab -> Zab -> Bool
  (==) Zib Zib = True
  (==) Zyb Zyb = True
  (==) Zob Zob = True
  (==) Zub Zub = True
  (==) Zeb Zeb = True
  (==) _ _     = False
  
  Did we save much writing? Not a lot so far but this will really start to
  shine when we can omit the data constructor list to eqDef and when we can use
  this on types that contain types with Eq instances. -}

  borb1 : Zib == Zib = True
  borb1 = Refl
 
  borb2 : Zob == Zob = True
  borb2 = Refl

  borb3 : Zeb == Zyb = False
  borb3 = Refl
  



