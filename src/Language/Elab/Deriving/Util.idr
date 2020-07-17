module Language.Elab.Deriving.Util

import Language.Reflection

import Data.Strings

import Util

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


-- a0, b0, c0 .. a1,b1,c1 ..

fef : (a -> b -> c) -> Stream a -> List b -> Stream (List c)
fef f (x :: xs) ys = map (f x) ys :: fef f xs ys

rar : Stream (List c) -> Stream c
rar ([] :: xss) = rar xss
rar ((x :: xs) :: xss) = x :: rar (xs :: xss)

-- There's probably a better way to do this, I'm a little weak on how strictness
-- works
||| Provides an endless sequence of variable names
-- a0,b0..z0, a1,b1..z1, ...
export
infVars : Stream String
infVars = let c = [0,1..] {a=Int}
              d = ['a'..'z']
          in rar (fef (\x,y => strCons y "" ++ show x) c d)

