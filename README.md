Elab Deriving (bad name, pick better)
=====

Very WIP!

Resources:
https://github.com/mb64/idris2-extras/blob/main/Extra/Language/Derive.idr
https://github.com/david-christiansen/derive-all-the-instances

This is a package for deriving implementations of common functions and interfaces in [Idris2](https://github.com/idris-lang/Idris2). It's intended to alleviate the tedium of writing your own instances, especially for things like newtypes which is just a whole lot of copypasting of wrapping.

It's pretty basic just now but so is elaborator reflection.

Version
-------

This package follows [Haskell PVP](https://pvp.haskell.org/) which is distinct from [SEMVER](https://semver.org/) in that when examining `1.2.3`, `1.2`  is the Major Version rather than `1`.
