module Categories.GlobeCategory where

open import Data.Nat
open import Data.Nat.Properties using (<-trans)
open import Relation.Binary.PropositionalEquality

open import Categories



<-trans-assoc : {i j k l : ℕ} (ij : i < j) (jk : j < k) (kl : k < l) → <-trans (<-trans ij jk) kl ≡ <-trans ij (<-trans jk kl)
<-trans-assoc ij jk kl = {!!}


data GlobeHoms : ℕ → ℕ → Set where
  ident : (i : ℕ) → GlobeHoms i i
  source : (i j : ℕ) → i < j → GlobeHoms i j
  target : (i j : ℕ) → i < j → GlobeHoms i j


globe : (n : ℕ) → Category
globe n = makeCat ℕ GlobeHoms ident gcompose id-l id-r assoc where
  gcompose : {i j k : ℕ} → GlobeHoms j k → GlobeHoms i j → GlobeHoms i k
  gcompose {i} {.k} {k} (ident .k) f = f
  gcompose {.j} {j} {k} g (ident .j) = g
  gcompose {i} {j} {k} (source .j .k y) (source .i .j y') = source i k (<-trans y' y)
  gcompose {i} {j} {k} (source .j .k y) (target .i .j y') = source i k (<-trans y' y)
  gcompose {i} {j} {k} (target .j .k y) (source .i .j y') = target i k (<-trans y' y)
  gcompose {i} {j} {k} (target .j .k y) (target .i .j y') = target i k (<-trans y' y)

  id-l : {x y : ℕ} (f : GlobeHoms x y) → gcompose (ident y) f ≡ f
  id-l f = refl
  id-r : {x y : ℕ} (f : GlobeHoms x y) → gcompose f (ident x) ≡ f
  id-r {.y} {y} (ident .y) = refl
  id-r {x} {y} (source .x .y y') = refl
  id-r {x} {y} (target .x .y y') = refl
  assoc : {w x y z : ℕ} (h : GlobeHoms y z) (g : GlobeHoms x y) (f : GlobeHoms w x) → gcompose h (gcompose g f) ≡ gcompose (gcompose h g) f
  assoc h g f = {!!}