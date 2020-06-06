module Language.Elab.Deriving.Util

import Language.Reflection

import Data.Strings

%language ElabReflection


-- try making conditionals here, like

wrapShow : Show a => String -> String -> a -> String
-- which wraps with given parens if a constructor doesn't have arguments

-- e.g. Just x = "(Just x)"  Nothing = "Nothing"


-----------------------------

-- No good, all the ways I can think of to do this complain about
-- ElabReflection not being enabled. I don't really want users to have to turn
-- that on to use my Elab-defined things.

-- to use fastAppend without importing it at use-site
private
stringConcat : List String -> String
stringConcat = fastAppend

private
moduleNameElab : Elab String
moduleNameElab = do
  [((NS ns _),_)] <- getType `{{moduleName}}
    | [] => fail "moduleName is not in scope"
    | _ => fail "moduleName is not unique in scope"
  pure (stringConcat . intersperse "." . reverse $ ns)


