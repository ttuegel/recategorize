{-

Copyright 2017 Thomas Tuegel

This file is part of recategorize.

recategorize is free software: you can redistribute it and/or modify
it under the terms of the GNU Lesser General Public License as published by
the Free Software Foundation, either version 3 of the License, or
(at your option) any later version.

recategorize is distributed in the hope that it will be useful,
but WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
GNU Lesser General Public License for more details.

You should have received a copy of the GNU Lesser General Public License
along with Foobar.  If not, see <http://www.gnu.org/licenses/>.

-}

{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}

module Category
  ( Category(..)
  , (:-), imply, given
  , Vacuous
  ) where

import GHC.Exts

newtype (:-) (a :: Constraint) (b :: Constraint) = Imply { given :: forall r. (b => r) -> (a => r) }

imply = Imply

class Category (cat :: k -> k -> *) where
  type Obj cat :: k -> Constraint
  source :: cat a b -> (() :- Obj cat a)
  target :: cat a b -> (() :- Obj cat b)
  id :: Obj cat a => cat a a
  (>>>) :: cat a b -> cat b c -> cat a c
  (<<<) :: cat b c -> cat a b -> cat a c

  (>>>) f g = (<<<) g f
  (<<<) g f = (>>>) f g

class Vacuous (a :: k)
instance Vacuous a

instance Category (->) where
  type Obj (->) = Vacuous
  id = \a -> a
  source _ = imply (\r -> r)
  target _ = imply (\r -> r)
  (>>>) f g = \x -> g (f x)

instance Category (:-) where
  type Obj (:-) = Vacuous
  id = imply (\a -> a)
  source _ = imply (\r -> r)
  target _ = imply (\r -> r)
  (>>>) f g = imply (\c -> given f (given g c))
