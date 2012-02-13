module KanExtension where

open import Function
open import Level

open import Categories
open import Functors
open import Misc
open import NaturalTransformations
open import NaturalTransformations.Equality
open existsUnique



record IsRightKanExtension {ℓ₁ ℓ′₁ ℓ₂ ℓ′₂ ℓ₃ ℓ′₃ : Level}
  {C : Category {ℓ₁} {ℓ′₁}} {D : Category {ℓ₂} {ℓ′₂}} {S : Category {ℓ₃} {ℓ′₃}}
  (F : Functor C D) (X : Functor C S) (R : Functor D S)
  (Θ : NatTrans (R ⊙ F) X) : Set (ℓ₁ ⊔ ℓ′₁ ⊔ ℓ₂ ⊔ ℓ′₂ ⊔ ℓ₃ ⊔ ℓ′₃) where

  constructor make-RightKanExtension

  field
    factorisations : (R′ : Functor D S) (Θ′ : NatTrans (R′ ⊙ F) X) → existsUnique (NatTrans R′ R) _≡₂_ (λ Φ → Θ′ ≡₂ Θ •̂ (Φ ⊙̂ idNatTrans F))

  witnesses : (R′ : Functor D S) (Θ′ : NatTrans (R′ ⊙ F) X) → NatTrans R′ R
  witnesses R′ Θ′ = witness (factorisations R′ Θ′)

  satisfactions : (R′ : Functor D S) (Θ′ : NatTrans (R′ ⊙ F) X) → Θ′ ≡₂ Θ •̂ (witnesses R′ Θ′ ⊙̂ idNatTrans F)
  satisfactions R′ Θ′ = satisfaction (factorisations R′ Θ′)

  uniquenesses : (R′ : Functor D S) (Θ′ : NatTrans (R′ ⊙ F) X) (W′ : NatTrans R′ R) → Θ′ ≡₂ Θ •̂ (W′ ⊙̂ idNatTrans F) → W′ ≡₂ witnesses R′ Θ′
  uniquenesses R′ Θ′ = uniqueness (factorisations R′ Θ′)
  

{-
make-RightKanExtension : {ℓ₁ ℓ′₁ ℓ₂ ℓ′₂ ℓ₃ ℓ′₃ : Level}
  {C : Category {ℓ₁} {ℓ′₁}} {D : Category {ℓ₂} {ℓ′₂}} {S : Category {ℓ₃} {ℓ′₃}}
  (F : Functor C D) (X : Functor C S) (R : Functor D S)
  (Θ : NatTrans (R ⊙ F) X)
  (W : (R′ : Functor D S) (Θ′ : NatTrans (R′ ⊙ F) X) → NatTrans R′ R)
  (E : (R′ : Functor D S) (Θ′ : NatTrans (R′ ⊙ F) X) → Θ′ ≡₂ Θ •̂ (W R′ Θ′ ⊙̂ idNatTrans F))
  (U : (R′ : Functor D S) (Θ′ : NatTrans (R′ ⊙ F) X) (W′ : NatTrans R′ R) → Θ′ ≡₂ Θ •̂ (W′ ⊙̂ idNatTrans F) → W′ ≡₂ W R′ Θ′) → IsRightKanExtension F X R Θ
make-RightKanExtension F X R Θ W E U R′ Θ′ = make-unique (λ Φ → Θ′ ≡₂ Θ •̂ (Φ ⊙̂ idNatTrans F)) (W R′ Θ′) (E R′ Θ′) (U R′ Θ′)
-}


IsLeftKanExtension : {ℓ₁ ℓ′₁ ℓ₂ ℓ′₂ ℓ₃ ℓ′₃ : Level}
  {C : Category {ℓ₁} {ℓ′₁}} {D : Category {ℓ₂} {ℓ′₂}} {S : Category {ℓ₃} {ℓ′₃}}
  (F : Functor C D) (X : Functor C S) (L : Functor D S)
  (Θ : NatTrans X (L ⊙ F)) → Set (ℓ₁ ⊔ ℓ′₁ ⊔ ℓ₂ ⊔ ℓ′₂ ⊔ ℓ₃ ⊔ ℓ′₃)

IsLeftKanExtension F X L Θ = IsRightKanExtension (functor-op F) (functor-op X) (functor-op L) (nat-trans-op Θ)
