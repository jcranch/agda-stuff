module Categories.Join.Properties where

open import Data.Sum
open import Level
open import Relation.Binary.PropositionalEquality

open import Categories
open import Categories.Join
open import Categories.Diagrams
open import Functors


∅-unit-l : {ℓ₁ ℓ′₁ : Level} (C : Category {ℓ₁} {ℓ′₁}) → Functor (∅ ✫ C) C
∅-unit-l C = makeFunctor obj hom id compose where
  obj : Category.obj (∅ ✫ C) → Category.obj C
  obj (inj₁ ())
  obj (inj₂ y) = y
  hom : {x y : Category.obj (∅ ✫ C)} → Category.hom (∅ ✫ C) x y → Category.hom C (obj x) (obj y)
  hom (j-inj₁ () y f)
  hom (j-inj₂ x y f) = f
  hom (j-inj₁₂ () y)
  id : (x : Category.obj (∅ ✫ C)) → hom (Category.id (∅ ✫ C) x) ≡ Category.id C (obj x)
  id (inj₁ ())
  id (inj₂ y) = refl
  compose : {x y z : Category.obj (∅ ✫ C)} (g : Category.hom (∅ ✫ C) y z) (f : Category.hom (∅ ✫ C) x y) → hom (Category.compose (∅ ✫ C) g f) ≡ Category.compose C (hom g) (hom f)
  compose (j-inj₁ () y g) f
  compose (j-inj₁₂ () y) f
  compose (j-inj₂ x y g) (j-inj₁₂ () .x)
  compose (j-inj₂ y z g) (j-inj₂ x .y f) = refl

∅-unit-r : {ℓ₁ ℓ′₁ : Level} (C : Category {ℓ₁} {ℓ′₁}) → Functor (C ✫ ∅) C
∅-unit-r C = makeFunctor obj hom id compose where
  obj : Category.obj (C ✫ ∅) → Category.obj C
  obj (inj₁ x) = x
  obj (inj₂ ())
  hom : {x y : Category.obj (C ✫ ∅)} → Category.hom (C ✫ ∅) x y → Category.hom C (obj x) (obj y)
  hom (j-inj₁ x y f) = f
  hom (j-inj₂ () y f)
  hom (j-inj₁₂ x ())
  id : (x : Category.obj (C ✫ ∅)) → hom (Category.id (C ✫ ∅) x) ≡ Category.id C (obj x)
  id (inj₁ x) = refl
  id (inj₂ ())
  compose : {x y z : Category.obj (C ✫ ∅)} (g : Category.hom (C ✫ ∅) y z) (f : Category.hom (C ✫ ∅) x y) → hom (Category.compose (C ✫ ∅) g f) ≡ Category.compose C (hom g) (hom f)
  compose (j-inj₁ y z g) (j-inj₁ x .y f) = refl
  compose (j-inj₂ y () g) f
  compose (j-inj₁₂ y ()) f
