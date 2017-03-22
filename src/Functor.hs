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

{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeInType #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}

module Functor where

import Category

class (Category (Cod f), Category (Dom f)) => Functor (f :: j -> k) where
  type Dom f :: Cat j
  type Cod f :: Cat k
  map :: Dom f a b -> Cod f (f a) (f b)

functor :: forall f a. Functor f => Obj (Dom f) a :- Obj (Cod f) (f a)
functor = imply (\r -> given (source (map (id :: Dom f a a) :: Cod f (f a) (f a))) r)

class (Functor f, Dom f ~ p, Cod f ~ q) => FunctorOf (p :: Cat j) (q :: Cat k) (f :: j -> k)
instance (Functor f, Dom f ~ p, Cod f ~ q) => FunctorOf p q f

data Nat (p :: Cat j) (q :: Cat k) (f :: j -> k) (g :: j -> k) where
  Nat :: (FunctorOf p q f, FunctorOf p q g) => { transform :: forall a. Obj p a => Cod f (f a) (g a) } -> Nat p q f g

instance Category (Nat p q) where
  type Obj (Nat p q) = FunctorOf p q
  source (Nat _) = imply (\r -> r)
  target (Nat _) = imply (\r -> r)
  id = Nat (map id)
  (>>>) f g = given (source f)
              (given (target g)
               (given (target f)
                (Nat (transform f >>> transform g))))

type family NatDom (p :: Cat (i -> j)) :: Cat i where
  NatDom (Nat p q) = p

type family NatCod (p :: Cat (i -> j)) :: Cat j where
  NatCod (Nat p q) = q

class (p ~ Nat (NatDom p) (NatCod p), Category (NatDom p), Category (NatCod p)) => Natural (p :: Cat (i -> j))
instance (p ~ Nat (NatDom p) (NatCod p), Category (NatDom p), Category (NatCod p)) => Natural (p :: Cat (i -> j))

class (Functor p, Natural (Cod p)) => Bifunctor (p :: i -> j -> k)
instance (Functor p, Natural (Cod p)) => Bifunctor (p :: i -> j -> k)

lmap :: forall p a b c. (Bifunctor p, Obj (NatDom (Cod p)) c) => Dom p a b -> NatCod (Cod p) (p a c) (p b c)
lmap f =
  (given (source f)
   (given (functor :: Obj (Dom p) a :- Obj (Cod p) (p a))
    (transform (map f))))

rmap :: forall p a b c. (Bifunctor p, Obj (Dom p) c) => NatDom (Cod p) a b -> NatCod (Cod p) (p c a) (p c b)
rmap f =
  (given (functor :: Obj (Dom p) c :- Obj (Cod p) (p c))
   (map f))

bimap :: Bifunctor p => Dom p a b -> NatDom (Cod p) c d -> NatCod (Cod p) (p a c) (p b d)
bimap f g =
  (given (target f)
   (given (source g)
    (lmap f >>> rmap g)))
