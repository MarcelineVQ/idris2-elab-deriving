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

-- Ideally we would query for these with some reflection mechanism
fooCons : List TTImp
fooCons = [`(Biz), `(Baz)]

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
eqConClause : (lhs : TTImp) -> (rhs : TTImp) -> Clause
eqConClause con b = PatClause EmptyFC
                      con (ICase EmptyFC b `(Foo) [isConPat con, elseFalse])
              -- e.g. Biz => case b of
              --               Biz => True
              --               _   => False

-- The body of (==)
eqDef : TTImp -> TTImp -> TTImp
eqDef a b = ICase EmptyFC a `(Foo)
              (map (\c => eqConClause c b) fooCons  )
          -- e.g. case a of
          --        Biz => case b of
          --                 Biz => True
          --                 _   => False
          --        Baz => case b of
          --                 Baz => True
          --                 _   => False

-- Even things like this logMsg should be elaborated instead of hard coded
elabEq : Foo -> Foo -> Bool
elabEq a b = %runElab do logMsg 1 "Reflection elaborating == for Foo"
                         check (eqDef `(a) `(b))
-- voila
(==) : Foo -> Foo -> Bool
(==) = elabEq






