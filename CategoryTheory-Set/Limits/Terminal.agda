module Limits.Terminal where

open import Level
open import Relation.Binary.PropositionalEquality

open import Limits
open import Categories
open import Categories.Diagrams
open import Categories.Join
open import Categories.Join.Properties
open import Functors
open import Misc
open import NaturalTransformations



IsTerminal : {ℓ₁ ℓ′₁ : Level} (C : Category {ℓ₁} {ℓ′₁}) → Category.obj C → Set (ℓ₁ ⊔ ℓ′₁)
IsTerminal C x = IsLimit {C = C} ∅-functor x ∅-nat-trans


record IsTerminal-lowbrow {ℓ₁ ℓ′₁ : Level} (C : Category {ℓ₁} {ℓ′₁}) (⊤ : Category.obj C) : Set (ℓ₁ ⊔ ℓ′₁) where
  constructor lowbrow-1
  field
    exists-to-1 : (x : Category.obj C) → Category.hom C x ⊤
    unique-to-1 : {x : Category.obj C} (f : Category.hom C x ⊤) → f ≡ exists-to-1 x


terminal↓ : {ℓ₁ ℓ′₁ : Level} {C : Category {ℓ₁} {ℓ′₁}} (x : Category.obj C) → IsTerminal C x → IsTerminal-lowbrow C x
terminal↓ {C = C} x t = lowbrow-1 (λ a → IsLimit.witnesses t a ∅-nat-trans) (λ {a} f → IsLimit.uniquenesses t a ∅-nat-trans f (λ ()))


terminal↑ : {ℓ₁ ℓ′₁ : Level} {C : Category {ℓ₁} {ℓ′₁}} (x : Category.obj C) → IsTerminal-lowbrow C x → IsTerminal C x
terminal↑ x (lowbrow-1 exists-to-1 unique-to-1) = make-Limit (λ a _ → makeUnique (exists-to-1 a) (λ ()) (λ f _ → unique-to-1 f))


IsInitial : {ℓ₁ ℓ′₁ : Level} (C : Category {ℓ₁} {ℓ′₁}) → Category.obj C → Set (ℓ₁ ⊔ ℓ′₁)
IsInitial C x = IsTerminal (opposite C) x


module low-from-high {ℓ₁ ℓ′₁ : Level} (C : Category {ℓ₁} {ℓ′₁}) (x : Category.obj C) (t : IsTerminal C x) where
  open IsTerminal-lowbrow (terminal↓ {C = C} x t) public
open low-from-high public
