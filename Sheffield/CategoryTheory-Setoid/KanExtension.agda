module Sheffield.CategoryTheory-Setoid.KanExtension where

open import Data.Unit using (tt)
open import Level
open import Relation.Binary

open import Sheffield.CategoryTheory-Setoid.Categories
open import Sheffield.CategoryTheory-Setoid.Categories.Diagrams
open import Sheffield.CategoryTheory-Setoid.Comma
open import Sheffield.CategoryTheory-Setoid.Functors
open import Sheffield.CategoryTheory-Setoid.Functors.Category
open import Sheffield.CategoryTheory-Setoid.Terminal


extensions : {ℓ₁ ℓ′₁ ℓ″₁ ℓ₂ ℓ′₂ ℓ″₂ ℓ₃ ℓ′₃ ℓ″₃ : Level} {C : Category {ℓ₁} {ℓ′₁} {ℓ″₁}} {D : Category {ℓ₂} {ℓ′₂} {ℓ″₂}} {S : Category {ℓ₃} {ℓ′₃} {ℓ″₃}} (F : Functor C D) (X : Functor C S) → Category {ℓ₁ ⊔ ℓ′₁ ⊔ ℓ″₁ ⊔ ℓ₂ ⊔ ℓ′₂ ⊔ ℓ″₂ ⊔ ℓ₃ ⊔ ℓ′₃ ⊔ ℓ″₃} {ℓ₁ ⊔ ℓ₂ ⊔ ℓ′₂ ⊔ ℓ″₂ ⊔ ℓ₃ ⊔ ℓ′₃ ⊔ ℓ″₃} {ℓ₂ ⊔ ℓ″₃}
extensions {C = C} {D = D} {S = S} F X = Comma (precomposition C D S F) (constFunctor point (Functors C S) X)





record IsKanExtension {ℓ₁ ℓ′₁ ℓ″₁ ℓ₂ ℓ′₂ ℓ″₂ ℓ₃ ℓ′₃ ℓ″₃ : Level} {C : Category {ℓ₁} {ℓ′₁} {ℓ″₁}} {D : Category {ℓ₂} {ℓ′₂} {ℓ″₂}} {S : Category {ℓ₃} {ℓ′₃} {ℓ″₃}} (F : Functor C D) (X : Functor C S) (L : Category.obj (extensions F X)) : Set (ℓ₁ ⊔ ℓ′₁ ⊔ ℓ″₁ ⊔ ℓ₂ ⊔ ℓ′₂ ⊔ ℓ″₂ ⊔ ℓ₃ ⊔ ℓ′₃ ⊔ ℓ″₃) where

  constructor make-IsKanExtension

  field
    kan-property : IsTerminal (extensions F X) L

  functor : Functor D S
  functor = Functor.obj (Proj₁ (precomposition C D S F) (constFunctor point (Functors C S) X)) L





record KanExtension {ℓ₁ ℓ′₁ ℓ″₁ ℓ₂ ℓ′₂ ℓ″₂ ℓ₃ ℓ′₃ ℓ″₃ : Level} {C : Category {ℓ₁} {ℓ′₁} {ℓ″₁}} {D : Category {ℓ₂} {ℓ′₂} {ℓ″₂}} {S : Category {ℓ₃} {ℓ′₃} {ℓ″₃}} (F : Functor C D) (X : Functor C S) : Set (ℓ₁ ⊔ ℓ′₁ ⊔ ℓ″₁ ⊔ ℓ₂ ⊔ ℓ′₂ ⊔ ℓ″₂ ⊔ ℓ₃ ⊔ ℓ′₃ ⊔ ℓ″₃) where

  constructor make-KanExtension

  field
    extension : Category.obj (extensions F X)
    isKanExtension : IsKanExtension F X extension

  open IsKanExtension isKanExtension