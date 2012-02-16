module Sheffield.CategoryTheory-Set.Categories.GlobeCategory where

open import Data.Nat
open import Data.Nat.Properties using (<-trans)
open import Relation.Binary.PropositionalEquality

open import Sheffield.CategoryTheory-Set.Categories



<-unique : {i j : ℕ} (a b : i ≤ j) → a ≡ b
<-unique z≤n z≤n = refl
<-unique (s≤s a) (s≤s b) = cong s≤s (<-unique a b)

<-trans-assoc : {i j k l : ℕ} {ij : i < j} {jk : j < k} {kl : k < l} → <-trans (<-trans ij jk) kl ≡ <-trans ij (<-trans jk kl)
<-trans-assoc {ij = ij} {jk} {kl} = <-unique (<-trans (<-trans ij jk) kl) (<-trans ij (<-trans jk kl))


data GlobeHoms : ℕ → ℕ → Set where
  ident : (i : ℕ) → GlobeHoms i i
  source : {i j : ℕ} → i < j → GlobeHoms i j
  target : {i j : ℕ} → i < j → GlobeHoms i j


globe : (n : ℕ) → Category
globe n = makeCat ℕ GlobeHoms ident gcompose id-l id-r assoc where
  gcompose : {i j k : ℕ} → GlobeHoms j k → GlobeHoms i j → GlobeHoms i k
  gcompose {i} {.k} {k} (ident .k) f = f
  gcompose {.j} {j} {k} g (ident .j) = g
  gcompose {i} {j} {k} (source y) (source y') = source (<-trans y' y)
  gcompose {i} {j} {k} (source y) (target y') = source (<-trans y' y)
  gcompose {i} {j} {k} (target y) (source y') = target (<-trans y' y)
  gcompose {i} {j} {k} (target y) (target y') = target (<-trans y' y)

  id-l : {x y : ℕ} (f : GlobeHoms x y) → gcompose (ident y) f ≡ f
  id-l f = refl
  id-r : {x y : ℕ} (f : GlobeHoms x y) → gcompose f (ident x) ≡ f
  id-r {.y} {y} (ident .y) = refl
  id-r {x} {y} (source _) = refl
  id-r {x} {y} (target _) = refl
  assoc : {w x y z : ℕ} (h : GlobeHoms y z) (g : GlobeHoms x y) (f : GlobeHoms w x) → gcompose h (gcompose g f) ≡ gcompose (gcompose h g) f
  assoc {w} {x} {.z} {z} (ident .z) g f = refl
  assoc {w} {.y} {y} {z} (source y') (ident .y) f = refl
  assoc {.x} {x} {y} {z} (source y') (source y0) (ident .x) = refl
  assoc {w} {x} {y} {z} (source y') (source y0) (source y1) = cong source <-trans-assoc
  assoc {w} {x} {y} {z} (source y') (source y0) (target y1) = cong source <-trans-assoc
  assoc {.x} {x} {y} {z} (source y') (target y0) (ident .x) = refl
  assoc {w} {x} {y} {z} (source y') (target y0) (source y1) = cong source <-trans-assoc
  assoc {w} {x} {y} {z} (source y') (target y0) (target y1) = cong source <-trans-assoc
  assoc {w} {.y} {y} {z} (target y') (ident .y) f = refl
  assoc {.x} {x} {y} {z} (target y') (source y0) (ident .x) = refl
  assoc {w} {x} {y} {z} (target y') (source y0) (source y1) = cong target <-trans-assoc
  assoc {w} {x} {y} {z} (target y') (source y0) (target y1) = cong target <-trans-assoc
  assoc {.x} {x} {y} {z} (target y') (target y0) (ident .x) = refl
  assoc {w} {x} {y} {z} (target y') (target y0) (source y1) = cong target <-trans-assoc
  assoc {w} {x} {y} {z} (target y') (target y0) (target y1) = cong target <-trans-assoc