module Language.Elab.Deriving

import Language.Reflection

import Language.Elab.Deriving.Eq
-- import Language.Elab.Deriving.Ord
import Language.Elab.Deriving.Show

%language ElabReflection

-- the handy regex for eliminating FC from tests: \(MkFC.+?\)\)\s
-- another form: \(MkFC \"\(interactive\)\" \([\s\S]*?\) \([\s\S]*?\)\) 

-- In Newtype the method being used is to create the implementation record only,
-- as opposed to Show and Eq where we created the functions in the module scope
-- and then refereed to them in the record. The method of this module is likely
-- the better way to go to avoid namespace pollution. But worse for inspecting
-- the methods directly.


-- Eventually this module will house the generic 'derive' mechanism, allowing
-- for this sort of thing:
-- derive `{{Foo}} Export [Eq,Show,Ord]
-- customizable in this fashion
-- derive `{{Foo}} Export [Eq,Ord]
-- derive `{{Foo}} Private [Show]

-- don't forget to have newtype deriving too! There's no reason we should have
-- to write up instances ourselves when the type we wrap has an instance.

-- deriving via would be neat too, how do?

-- derive functor, and applicative and monad

derivable : Type -> (Visibility -> Name -> Elab ())
derivable (Eq a) = deriveEq
derivable (Show a) = deriveShow
derivable t = \_,_ => fail "Given a (currently) non-derivable interface."

-- sort instances by requirments, e.g. (1,Eq), (2,Ord) etc

-- export
-- deriving : Visibility -> Name -> Type -> Elab ()
-- deriving vis nam ty = do
  -- let fun = derivable ty


{-

This pattern comes up a lot

isNoSugar : UnelabMode -> Bool
isNoSugar (NoSugar _) = True
isNoSugar _ = False
isDefImp : PiInfo t -> Bool
isDefImp (DefImplicit _) = True
isDefImp _ = False

We should have a deriving or converstion for this sort of thing, where you
select the 'true' case and all others are false. e.g.

data Foo : Type where
  Bif : Foo
  Waf : Int -> Foo

deriveSelectors Foo
results in

isBif : Foo -> Bool
isBif Bif = True
isBif _ = False

isWaf : Foo -> Bool
isWaf (Waf _) = True
isWaf _ = False

-}