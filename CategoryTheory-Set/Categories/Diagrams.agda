module Categories.Diagrams where

  -- Some useful finite categories

open import Data.Empty
open import Data.Unit
open import Data.Sum renaming (_⊎_ to _+_)
open import Level
open import Relation.Binary.PropositionalEquality as PropEq using (_≡_ ; refl)

open import Categories
open import Categories.Join
open import Categories.Parallel
open import Categories.Sum
open import Functors



∅ : Category {zero} {zero}
∅ = makeCat ⊥ ⊥-elim (λ ()) (λ {x} {y} → λ {}) (λ {x} → λ {}) (λ {x} → λ {}) (λ {w} {x} {y} → λ {})


point : Category
point = makeCat ⊤ (λ _ _ → ⊤) (λ _ → tt) (λ _ _ → tt) (λ _ → refl) (λ _ → refl) (λ _ _ _ → refl)


2points : Category
2points = point ⊎ point

2points-functor : {ℓ₁ ℓ′₁ : Level} {C : Category {ℓ₁} {ℓ′₁}} (α β : Category.obj C) → Functor 2points C
2points-functor {C = C} α β = ⊎-functor (constFunctor point C α) (constFunctor point C β)



↗↖ : Category
↗↖ = 2points ✫ point


↙↘ : Category
↙↘ = point ✫ 2points


⇉ : Category
⇉ = parallels (⊤ + ⊤)