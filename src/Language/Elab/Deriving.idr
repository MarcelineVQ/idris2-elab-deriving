module Language.Elab.Deriving

import Language.Reflection

%language ElabReflection

-- Elaboration for == for Foo. Next step is to be able to have this work on
-- more complex types like
-- data Foo : Type -> Type where
--   Bob : a -> Foo a

-----------------------------

-- Elaboration for == for Foo

export
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

-- when it did not
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

iVar : Name -> TTImp
iVar n = IVar EmptyFC n

-- export is default for now, expect that to change/be customizable
eqDecl : TTImp -> List TTImp -> Elab ()
eqDecl ty vars
  = declare `[ export
               (==) : ~(ty) -> ~(ty) -> Bool
               (==) x y = ~(eqDef ty vars `(x) `(y)) ] 

export
deriveEq : (n : Name) -> Elab ()
deriveEq n = do cons@(_::_) <- getCons n
                  | [] => fail $ show n ++ " doesn't have constructors to equate"
                traverse (\x => logMsg 1 (show x)) cons
                eqDecl (iVar n) (map iVar cons)

export
data New : Type -> Type where
  MkNew : a -> New a

-- %runElab (deriveEq `{{Language.Elab.Deriving.New}})

-- use variable lookup to pass `(Foo) or `{{Foo}}` instead and lookup Language.Elab.Deriving.Foo
namespace Foo
  %runElab (deriveEq `{{Language.Elab.Deriving.Foo}})
  -- Latest version of making ==, allowing your choice of type.

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
  
  -- The meat
  %runElab deriveEq `{{Language.Elab.Deriving.Zab.Zab}}

  {- -- written yourself
  (==) : Zab -> Zab -> Bool
  (==) Zib Zib = True
  (==) Zyb Zyb = True
  (==) Zob Zob = True
  (==) Zub Zub = True
  (==) Zeb Zeb = True
  (==) _ _     = False
  -}

  borb1 : Zib == Zib = True
  borb1 = Refl
 
  borb2 : Zob == Zob = True
  borb2 = Refl

  borb3 : Zeb == Zyb = False
  borb3 = Refl




