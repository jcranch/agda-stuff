module Sheffield.CategoryTheory-Setoid.Limits where

open import Data.Unit using (tt)
open import Level
open import Relation.Binary

open import Sheffield.CategoryTheory-Setoid.Categories
open import Sheffield.CategoryTheory-Setoid.Categories.Diagrams
open import Sheffield.CategoryTheory-Setoid.Comma
open import Sheffield.CategoryTheory-Setoid.Functors
open import Sheffield.CategoryTheory-Setoid.Functors.Category
open import Sheffield.CategoryTheory-Setoid.Terminal
open import Sheffield.CategoryTheory-Setoid.NaturalTransformations



cones : {ℓ₁ ℓ′₁ ℓ″₁ ℓ₂ ℓ′₂ ℓ″₂ : Level} {K : Category {ℓ₁} {ℓ′₁} {ℓ″₁}} {C : Category {ℓ₂} {ℓ′₂} {ℓ″₂}} (F : Functor K C) → Category {ℓ₁ ⊔ ℓ′₁ ⊔ ℓ″₁ ⊔ ℓ₂ ⊔ ℓ′₂ ⊔ ℓ″₂} {ℓ₁ ⊔ ℓ′₂ ⊔ ℓ″₂} {ℓ″₂}
cones {K = K} {C = C} F = Comma (constFunctors K C) (constFunctor point (Functors K C) F)



record IsLimit {ℓ₁ ℓ′₁ ℓ″₁ ℓ₂ ℓ′₂ ℓ″₂ : Level} {K : Category {ℓ₁} {ℓ′₁} {ℓ″₁}} {C : Category {ℓ₂} {ℓ′₂} {ℓ″₂}} (F : Functor K C) (L : Category.obj (cones F)) : Set (ℓ₁ ⊔ ℓ′₁ ⊔ ℓ″₁ ⊔ ℓ₂ ⊔ ℓ′₂ ⊔ ℓ″₂) where
  constructor make-IsLimit

  field
    limiting : IsTerminal (cones F) L

  object = comma-structure.Comma-obj.s _ _ L
  cone-trans = comma-structure.Comma-obj.f _ _ L



record Limit {ℓ₁ ℓ′₁ ℓ″₁ ℓ₂ ℓ′₂ ℓ″₂ : Level} {K : Category {ℓ₁} {ℓ′₁} {ℓ″₁}} {C : Category {ℓ₂} {ℓ′₂} {ℓ″₂}} (F : Functor K C) : Set (ℓ₁ ⊔ ℓ′₁ ⊔ ℓ″₁ ⊔ ℓ₂ ⊔ ℓ′₂ ⊔ ℓ″₂) where
  constructor makeLimit

  field
    cone : Category.obj (cones F)
    isLimit : IsLimit F cone

  open IsLimit isLimit public




record HasLimits-shape {ℓ₁ ℓ′₁ ℓ″₁ ℓ₂ ℓ′₂ ℓ″₂ : Level} (K : Category {ℓ₁} {ℓ′₁} {ℓ″₁}) (C : Category {ℓ₂} {ℓ′₂} {ℓ″₂}) : Set (ℓ₁ ⊔ ℓ′₁ ⊔ ℓ″₁ ⊔ ℓ₂ ⊔ ℓ′₂ ⊔ ℓ″₂) where

  field
    limit : (F : Functor K C) → Limit F
