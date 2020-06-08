module Language.Elab.Deriving

import Language.Reflection

%language ElabReflection

-- the handy regex for eliminating FC from tests: \(MkFC.+?\)\)\s





-- Eventually this module will house the generic 'derive' mechanism, allowing
-- for this sort of thing:
-- derive `{{Foo}} Export [Eq,Show,Ord]
-- customizable in this fashion
-- derive `{{Foo}} Export [Eq,Ord]
-- derive `{{Foo}} Private [Show]

-- don't forget to have newtype deriving too! There's no reason we should have
-- to write up instances ourselves when the type we wrap has an instance.


