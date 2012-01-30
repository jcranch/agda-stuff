module Categories.Parallel where

open import Level
open import Relation.Binary.PropositionalEquality as PropEq using (_≡_ ; refl)

open import Categories


parallels : {ℓ : Level} → Set ℓ → Category

data parallel-obj : Set where
  source : parallel-obj
  target : parallel-obj

data parallel-hom {ℓ : Level} (A : Set ℓ) : parallel-obj → parallel-obj → Set ℓ where
  id-s : parallel-hom A source source
  id-t : parallel-hom A target target
  parallel-map : A → parallel-hom A source target

parallels A  = makeCat parallel-obj (parallel-hom A) id compose id-l id-r assoc where
  id : (x : parallel-obj) → parallel-hom A x x
  id source = id-s
  id target = id-t
  compose : {x y z : parallel-obj} (g : parallel-hom A y z) (f : parallel-hom A x y) → parallel-hom A x z
  compose g id-s = g
  compose id-t f = f
  id-l : {x y : parallel-obj} (f : parallel-hom A x y) → compose (id y) f ≡ f
  id-l id-s = refl
  id-l id-t = refl
  id-l (parallel-map y) = refl
  id-r : {x y : parallel-obj} (f : parallel-hom A x y) → compose f (id x) ≡ f
  id-r {source} f = refl
  id-r {target} id-t = refl
  assoc : {w x y z : parallel-obj} (h : parallel-hom A y z) (g : parallel-hom A x y) (f : parallel-hom A w x) → compose h (compose g f) ≡ compose (compose h g) f
  assoc id-s () id-t
  assoc (parallel-map _) () id-t
  assoc (parallel-map _) () (parallel-map _)
  assoc id-s () (parallel-map _)
  assoc h g id-s = refl
  assoc id-t id-t id-t = refl
  assoc id-t id-t (parallel-map y) = refl
