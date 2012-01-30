module KanExtension where

open import Level
open import Relation.Binary

open import Categories
open import Functors
open import NaturalTransformations
open import NaturalTransformations.Equality





record IsUnique {α β ℓ : Level} {A : Set α} (_≈_ : Rel A ℓ) (P : A → Set β) (a : A) : Set (α ⊔ β ⊔ ℓ) where
  constructor make-it-unique
  field
    exists : P a
    unique : (a′ : A) → P a′ → a′ ≈ a

record ExistsUnique {α β ℓ : Level} (A : Set α) (_≈_ : Rel A ℓ) (P : A → Set β) : Set (α ⊔ β ⊔ ℓ) where
  constructor make-unique′
  field
    witness : A
    isUnique : IsUnique _≈_ P witness
  open IsUnique isUnique public

make-unique : {α β ℓ : Level} {A : Set α} {_≈_ : Rel A ℓ} (P : A → Set β) (a : A) → P a → ((a′ : A) → P a′ → a′ ≈ a) → ExistsUnique A _≈_ P
make-unique P a ∃ ! = make-unique′ a (make-it-unique ∃ !)

open ExistsUnique





IsRightKanExtension : {ℓ₁ ℓ′₁ ℓ₂ ℓ′₂ ℓ₃ ℓ′₃ : Level}
  {C : Category {ℓ₁} {ℓ′₁}} {D : Category {ℓ₂} {ℓ′₂}} {S : Category {ℓ₃} {ℓ′₃}}
  (F : Functor C D) (X : Functor C S) (R : Functor D S)
  (Θ : NatTrans (R ⊙ F) X) → Set (ℓ₁ ⊔ ℓ′₁ ⊔ ℓ₂ ⊔ ℓ′₂ ⊔ ℓ₃ ⊔ ℓ′₃)
IsRightKanExtension {_} {_} {_} {_} {_} {_} {C} {D} {S} F X R Θ = (R′ : Functor D S) (Θ′ : NatTrans (R′ ⊙ F) X) → ExistsUnique (NatTrans R′ R) _≡₂_ (λ Φ → Θ′ ≡₂ Θ •̂ (Φ ⊙̂ idNatTrans F))

make-RightKanExtension : {ℓ₁ ℓ′₁ ℓ₂ ℓ′₂ ℓ₃ ℓ′₃ : Level}
  {C : Category {ℓ₁} {ℓ′₁}} {D : Category {ℓ₂} {ℓ′₂}} {S : Category {ℓ₃} {ℓ′₃}}
  (F : Functor C D) (X : Functor C S) (R : Functor D S)
  (Θ : NatTrans (R ⊙ F) X)
  (W : (R′ : Functor D S) (Θ′ : NatTrans (R′ ⊙ F) X) → NatTrans R′ R)
  (E : (R′ : Functor D S) (Θ′ : NatTrans (R′ ⊙ F) X) → Θ′ ≡₂ Θ •̂ (W R′ Θ′ ⊙̂ idNatTrans F))
  (U : (R′ : Functor D S) (Θ′ : NatTrans (R′ ⊙ F) X) (W′ : NatTrans R′ R) → Θ′ ≡₂ Θ •̂ (W′ ⊙̂ idNatTrans F) → W′ ≡₂ W R′ Θ′) → IsRightKanExtension F X R Θ
make-RightKanExtension F X R Θ W E U R′ Θ′ = make-unique (λ Φ → Θ′ ≡₂ Θ •̂ (Φ ⊙̂ idNatTrans F)) (W R′ Θ′) (E R′ Θ′) (U R′ Θ′)



IsLeftKanExtension : {ℓ₁ ℓ′₁ ℓ₂ ℓ′₂ ℓ₃ ℓ′₃ : Level}
  {C : Category {ℓ₁} {ℓ′₁}} {D : Category {ℓ₂} {ℓ′₂}} {S : Category {ℓ₃} {ℓ′₃}}
  (F : Functor C D) (X : Functor C S) (L : Functor D S)
  (Θ : NatTrans X (L ⊙ F)) → Set (ℓ₁ ⊔ ℓ′₁ ⊔ ℓ₂ ⊔ ℓ′₂ ⊔ ℓ₃ ⊔ ℓ′₃)

IsLeftKanExtension F X L Θ = IsRightKanExtension (functor-op F) (functor-op X) (functor-op L) (nat-trans-op Θ)