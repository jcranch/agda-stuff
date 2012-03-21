module Sheffield.CategoryTheory-Setoid.Functors.Isomorphism where

open import Level
open import Relation.Binary
import Relation.Binary.EqReasoning

open import Sheffield.CategoryTheory-Setoid.Categories
open import Sheffield.CategoryTheory-Setoid.Functors
open import Sheffield.CategoryTheory-Setoid.NaturalTransformations
open import Sheffield.CategoryTheory-Setoid.NaturalTransformations.Equality
open import Sheffield.CategoryTheory-Setoid.NaturalTransformations.Properties


-- still to do: uniqueness of inverses


record Isomorphism₁ {ℓ₁ ℓ′₁ ℓ″₁ ℓ₂ ℓ′₂ ℓ″₂ : Level} {C : Category {ℓ₁} {ℓ′₁} {ℓ″₁}} {D : Category {ℓ₂} {ℓ′₂} {ℓ″₂}} {F G : Functor C D} (obverse : NatTrans F G) : Set (ℓ₁ ⊔ ℓ′₁ ⊔ ℓ″₁ ⊔ ℓ₂ ⊔ ℓ′₂ ⊔ ℓ″₂)  where
  constructor make-Iso₁
  field
    reverse : NatTrans G F
    unit : reverse •̂ obverse ≈₂ idNatTrans F
    counit : obverse •̂ reverse ≈₂ idNatTrans G


inverse₁ : {ℓ₁ ℓ′₁ ℓ″₁ ℓ₂ ℓ′₂ ℓ″₂ : Level} {C : Category {ℓ₁} {ℓ′₁} {ℓ″₁}} {D : Category {ℓ₂} {ℓ′₂} {ℓ″₂}} {F G : Functor C D} {Θ : NatTrans F G} → Isomorphism₁ Θ → NatTrans G F
inverse₁ = Isomorphism₁.reverse


Iso₁-refl : {ℓ₁ ℓ′₁ ℓ″₁ ℓ₂ ℓ′₂ ℓ″₂ : Level} {C : Category {ℓ₁} {ℓ′₁} {ℓ″₁}} {D : Category {ℓ₂} {ℓ′₂} {ℓ″₂}} (F : Functor C D) → Isomorphism₁ (idNatTrans F)
Iso₁-refl F = make-Iso₁ (idNatTrans F) (•̂-unit-l (idNatTrans F)) (•̂-unit-l (idNatTrans F))

Iso₁-sym : {ℓ₁ ℓ′₁ ℓ″₁ ℓ₂ ℓ′₂ ℓ″₂ : Level} {C : Category {ℓ₁} {ℓ′₁} {ℓ″₁}} {D : Category {ℓ₂} {ℓ′₂} {ℓ″₂}} {F G : Functor C D} {Θ : NatTrans F G} (I : Isomorphism₁ Θ) → Isomorphism₁ (inverse₁ I)
Iso₁-sym {Θ = Θ} (make-Iso₁ Θ⁻¹ c₁ c₂) = make-Iso₁ Θ c₂ c₁

Iso₁-trans : {ℓ₁ ℓ′₁ ℓ″₁ ℓ₂ ℓ′₂ ℓ″₂ : Level} {C : Category {ℓ₁} {ℓ′₁} {ℓ″₁}} {D : Category {ℓ₂} {ℓ′₂} {ℓ″₂}} {F G H : Functor C D} {Ξ : NatTrans G H} {Θ : NatTrans F G} (IΞ : Isomorphism₁ Ξ) (IΘ : Isomorphism₁ Θ) → Isomorphism₁ (Ξ •̂ Θ)
Iso₁-trans {D = D} (make-Iso₁ Ξ⁻¹ (make-≈₂ c₁) (make-≈₂ c₂)) (make-Iso₁ Θ⁻¹ (make-≈₂ c₃) (make-≈₂ c₄)) = make-Iso₁ (Θ⁻¹ •̂ Ξ⁻¹) (make-≈₂ (λ x → double-cancellation (c₃ x) (c₁ x))) (make-≈₂ (λ x → double-cancellation (c₂ x) (c₄ x))) where
  open Iso D




infix 4 _≅₁_
record _≅₁_ {ℓ₁ ℓ′₁ ℓ″₁ ℓ₂ ℓ′₂ ℓ″₂ : Level} {C : Category {ℓ₁} {ℓ′₁} {ℓ″₁}} {D : Category {ℓ₂} {ℓ′₂} {ℓ″₂}} (F G : Functor C D) : Set (ℓ₁ ⊔ ℓ′₁ ⊔ ℓ″₁ ⊔ ℓ₂ ⊔ ℓ′₂ ⊔ ℓ″₂) where
  constructor make-≅₁
  field
    obverse : NatTrans F G
    isIsomorphism₁ : Isomorphism₁ obverse
  open Isomorphism₁ isIsomorphism₁ public


isomorphic₁ : {ℓ₁ ℓ′₁ ℓ″₁ ℓ₂ ℓ′₂ ℓ″₂ : Level} {C : Category {ℓ₁} {ℓ′₁} {ℓ″₁}} {D : Category {ℓ₂} {ℓ′₂} {ℓ″₂}} {F G : Functor C D} (Θ : NatTrans F G) (Θ⁻¹ : NatTrans G F) → Θ⁻¹ •̂ Θ ≈₂ idNatTrans F → Θ •̂ Θ⁻¹ ≈₂ idNatTrans G → F ≅₁ G
isomorphic₁ Θ Θ⁻¹ unit counit = make-≅₁ Θ (make-Iso₁ Θ⁻¹ unit counit)



≅₁-refl : {ℓ₁ ℓ′₁ ℓ″₁ ℓ₂ ℓ′₂ ℓ″₂ : Level} {C : Category {ℓ₁} {ℓ′₁} {ℓ″₁}} {D : Category {ℓ₂} {ℓ′₂} {ℓ″₂}} (F : Functor C D) → F ≅₁ F
≅₁-refl F = make-≅₁ (idNatTrans F) (Iso₁-refl F)

≅₁-sym : {ℓ₁ ℓ′₁ ℓ″₁ ℓ₂ ℓ′₂ ℓ″₂ : Level} {C : Category {ℓ₁} {ℓ′₁} {ℓ″₁}} {D : Category {ℓ₂} {ℓ′₂} {ℓ″₂}} {F G : Functor C D} → F ≅₁ G → G ≅₁ F
≅₁-sym (make-≅₁ Θ I) = make-≅₁ (inverse₁ I) (Iso₁-sym I)

≅₁-trans : {ℓ₁ ℓ′₁ ℓ″₁ ℓ₂ ℓ′₂ ℓ″₂ : Level} {C : Category {ℓ₁} {ℓ′₁} {ℓ″₁}} {D : Category {ℓ₂} {ℓ′₂} {ℓ″₂}} {F G H : Functor C D} → F ≅₁ G → G ≅₁ H → F ≅₁ H
≅₁-trans (make-≅₁ Θ I) (make-≅₁ Ξ J) = make-≅₁ (Ξ •̂ Θ) (Iso₁-trans J I)

functors : {ℓ₁ ℓ′₁ ℓ″₁ ℓ₂ ℓ′₂ ℓ″₂ : Level} (C : Category {ℓ₁} {ℓ′₁} {ℓ″₁}) (D : Category {ℓ₂} {ℓ′₂} {ℓ″₂}) → Setoid (ℓ₁ ⊔ ℓ′₁ ⊔ ℓ″₁ ⊔ ℓ₂ ⊔ ℓ′₂ ⊔ ℓ″₂) (ℓ₁ ⊔ ℓ′₁ ⊔ ℓ″₁ ⊔ ℓ₂ ⊔ ℓ′₂ ⊔ ℓ″₂) 
functors C D = record {
  Carrier = Functor C D ;
  _≈_ = _≅₁_ ;
  isEquivalence = record {
    refl = λ {F} → ≅₁-refl F ;
    sym = ≅₁-sym ;
    trans = ≅₁-trans } }

module Functor-reasoning {ℓ₁ ℓ′₁ ℓ″₁ ℓ₂ ℓ′₂ ℓ″₂ : Level} (C : Category {ℓ₁} {ℓ′₁} {ℓ″₁}) (D : Category {ℓ₂} {ℓ′₂} {ℓ″₂}) = Relation.Binary.EqReasoning (functors C D)


