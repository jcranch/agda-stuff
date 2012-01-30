module Functors.Isomorphism where

open import Level
import Relation.Binary.EqReasoning

open import Categories
open import Functors
open import NaturalTransformations
open import NaturalTransformations.Equality
open import NaturalTransformations.Properties


-- still to do: uniqueness of inverses


data Isomorphism₁ {ℓ₁ ℓ₂ ℓ′₁ ℓ′₂ : Level} {C : Category {ℓ₁} {ℓ′₁}} {D : Category {ℓ₂} {ℓ′₂}} {F G : Functor C D} : (Θ : NatTrans F G) → Set (ℓ₁ ⊔ ℓ₂ ⊔ ℓ′₁ ⊔ ℓ′₂)  where
  makeIso₁ : (Θ : NatTrans F G) (Θ⁻¹ : NatTrans G F) → Θ⁻¹ •̂ Θ ≡₂ idNatTrans F → Θ •̂ Θ⁻¹ ≡₂ idNatTrans G → Isomorphism₁ Θ


infix 4 _≅₁_
data _≅₁_ {ℓ₁ ℓ₂ ℓ′₁ ℓ′₂ : Level} {C : Category {ℓ₁} {ℓ′₁}} {D : Category {ℓ₂} {ℓ′₂}} (F G : Functor C D) : Set (ℓ₁ ⊔ ℓ₂ ⊔ ℓ′₁ ⊔ ℓ′₂) where
  make-≅₁ : (Θ : NatTrans F G) → Isomorphism₁ Θ → F ≅₁ G


inverse₁ : {ℓ₁ ℓ₂ ℓ′₁ ℓ′₂ : Level} {C : Category {ℓ₁} {ℓ′₁}} {D : Category {ℓ₂} {ℓ′₂}} {F G : Functor C D} {Θ : NatTrans F G} → Isomorphism₁ Θ → NatTrans G F
inverse₁ (makeIso₁ Θ Θ⁻¹ _ _) = Θ⁻¹


Iso₁-refl : {ℓ₁ ℓ₂ ℓ′₁ ℓ′₂ : Level} {C : Category {ℓ₁} {ℓ′₁}} {D : Category {ℓ₂} {ℓ′₂}} (F : Functor C D) → Isomorphism₁ (idNatTrans F)
Iso₁-refl F = makeIso₁ (idNatTrans F) (idNatTrans F) (•̂-unit-l (idNatTrans F)) (•̂-unit-l (idNatTrans F))

Iso₁-sym : {ℓ₁ ℓ₂ ℓ′₁ ℓ′₂ : Level} {C : Category {ℓ₁} {ℓ′₁}} {D : Category {ℓ₂} {ℓ′₂}} {F G : Functor C D} {Θ : NatTrans F G} (I : Isomorphism₁ Θ) → Isomorphism₁ (inverse₁ I)
Iso₁-sym (makeIso₁ Θ Θ⁻¹ c₁ c₂) = makeIso₁ Θ⁻¹ Θ c₂ c₁

Iso₁-trans : {ℓ₁ ℓ₂ ℓ′₁ ℓ′₂ : Level} {C : Category {ℓ₁} {ℓ′₁}} {D : Category {ℓ₂} {ℓ′₂}} {F G H : Functor C D} {Ξ : NatTrans G H} {Θ : NatTrans F G} (IΞ : Isomorphism₁ Ξ) (IΘ : Isomorphism₁ Θ) → Isomorphism₁ (Ξ •̂ Θ)
Iso₁-trans {_} {ℓ₂} {_} {ℓ′₂} {_} {D} (makeIso₁ Ξ Ξ⁻¹ c₁ c₂) (makeIso₁ Θ Θ⁻¹ c₃ c₄) = makeIso₁ (Ξ •̂ Θ) (Θ⁻¹ •̂ Ξ⁻¹) (λ x → double-cancellation (c₃ x) (c₁ x)) (λ x → double-cancellation (c₂ x) (c₄ x)) where
  open Iso {ℓ₂} {ℓ′₂} {D}


Iso₁-⊙-left : {ℓ₁ ℓ₂ ℓ₃ ℓ′₁ ℓ′₂ ℓ′₃ : Level} {C : Category {ℓ₁} {ℓ′₁}} {D : Category {ℓ₂} {ℓ′₂}} {E : Category {ℓ₃} {ℓ′₃}} (G : Functor D E) (F F′ : Functor C D) {Θ : NatTrans F F′} (I : Isomorphism₁ Θ) → Isomorphism₁ (idNatTrans G ⊙̂ Θ)
Iso₁-⊙-left G F F′ (makeIso₁ Θ Θ⁻¹ c₁ c₂) = makeIso₁ (idNatTrans G ⊙̂ Θ) (idNatTrans G ⊙̂ Θ⁻¹) e₁ e₂ where
  e₁ = begin
         (idNatTrans G ⊙̂ Θ⁻¹) •̂ (idNatTrans G ⊙̂ Θ)
           ≈⟨ interchange (idNatTrans G) (idNatTrans G) Θ⁻¹ Θ ⟩
         (idNatTrans G •̂ idNatTrans G) ⊙̂ (Θ⁻¹ •̂ Θ)
           ≈⟨ ≡₂-⊙̂-left (idNatTrans G •̂ idNatTrans G) (idNatTrans G) (Θ⁻¹ •̂ Θ) (•̂-unit-l (idNatTrans G)) ⟩
         idNatTrans G ⊙̂ (Θ⁻¹ •̂ Θ)
           ≈⟨ ≡₂-⊙̂-right (idNatTrans G) (Θ⁻¹ •̂ Θ) (idNatTrans F) c₁ ⟩
         idNatTrans G ⊙̂ idNatTrans F
           ≈⟨ id⊙id≡₂id G F ⟩
         idNatTrans (G ⊙ F) ∎ where open Relation.Binary.EqReasoning (NaturalTransformations (G ⊙ F) (G ⊙ F))
  e₂ = begin
         (idNatTrans G ⊙̂ Θ) •̂ (idNatTrans G ⊙̂ Θ⁻¹)
           ≈⟨ interchange (idNatTrans G) (idNatTrans G) Θ Θ⁻¹ ⟩
         (idNatTrans G •̂ idNatTrans G) ⊙̂ (Θ •̂ Θ⁻¹)
           ≈⟨ ≡₂-⊙̂-left (idNatTrans G •̂ idNatTrans G) (idNatTrans G) (Θ •̂ Θ⁻¹) (•̂-unit-l (idNatTrans G)) ⟩
         idNatTrans G ⊙̂ (Θ •̂ Θ⁻¹)
           ≈⟨ ≡₂-⊙̂-right (idNatTrans G) (Θ •̂ Θ⁻¹) (idNatTrans F′) c₂ ⟩
         idNatTrans G ⊙̂ idNatTrans F′
           ≈⟨ id⊙id≡₂id G F′ ⟩
         idNatTrans (G ⊙ F′) ∎ where open Relation.Binary.EqReasoning (NaturalTransformations (G ⊙ F′) (G ⊙ F′))

Iso₁-⊙-right : {ℓ₁ ℓ₂ ℓ₃ ℓ′₁ ℓ′₂ ℓ′₃ : Level} {C : Category {ℓ₁} {ℓ′₁}} {D : Category {ℓ₂} {ℓ′₂}} {E : Category {ℓ₃} {ℓ′₃}} (G G′ : Functor D E) (F : Functor C D) {Θ : NatTrans G G′} (I : Isomorphism₁ Θ) → Isomorphism₁ (Θ ⊙̂ idNatTrans F)
Iso₁-⊙-right G G′ F (makeIso₁ Θ Θ⁻¹ c₁ c₂) = makeIso₁ (Θ ⊙̂ idNatTrans F) (Θ⁻¹ ⊙̂ idNatTrans F) e₁ e₂ where
  e₁ = begin
         (Θ⁻¹ ⊙̂ idNatTrans F) •̂ (Θ ⊙̂ idNatTrans F)
           ≈⟨ interchange Θ⁻¹ Θ (idNatTrans F) (idNatTrans F) ⟩
         (Θ⁻¹ •̂ Θ) ⊙̂ (idNatTrans F •̂ idNatTrans F) 
           ≈⟨ ≡₂-⊙̂-right (Θ⁻¹ •̂ Θ) (idNatTrans F •̂ idNatTrans F) (idNatTrans F) (•̂-unit-l (idNatTrans F)) ⟩
         (Θ⁻¹ •̂ Θ) ⊙̂ idNatTrans F
           ≈⟨ ≡₂-⊙̂-left (Θ⁻¹ •̂ Θ) (idNatTrans G) (idNatTrans F) c₁ ⟩
         idNatTrans G ⊙̂ idNatTrans F
           ≈⟨ id⊙id≡₂id G F ⟩
         idNatTrans (G ⊙ F) ∎ where open Relation.Binary.EqReasoning (NaturalTransformations (G ⊙ F) (G ⊙ F))
  e₂ = begin
         (Θ ⊙̂ idNatTrans F) •̂ (Θ⁻¹ ⊙̂ idNatTrans F)
           ≈⟨ interchange Θ Θ⁻¹ (idNatTrans F) (idNatTrans F) ⟩
         (Θ •̂ Θ⁻¹) ⊙̂ (idNatTrans F •̂ idNatTrans F) 
           ≈⟨ ≡₂-⊙̂-right (Θ •̂ Θ⁻¹) (idNatTrans F •̂ idNatTrans F) (idNatTrans F) (•̂-unit-l (idNatTrans F)) ⟩
         (Θ •̂ Θ⁻¹) ⊙̂ idNatTrans F
           ≈⟨ ≡₂-⊙̂-left (Θ •̂ Θ⁻¹) (idNatTrans G′) (idNatTrans F) c₂ ⟩
         idNatTrans G′ ⊙̂ idNatTrans F
           ≈⟨ id⊙id≡₂id G′ F ⟩
         idNatTrans (G′ ⊙ F) ∎ where open Relation.Binary.EqReasoning (NaturalTransformations (G′ ⊙ F) (G′ ⊙ F))


-- functor isomorphisms yield category isomorphisms
module iso-to-iso {ℓ₁ ℓ₂ ℓ′₁ ℓ′₂ : Level}
       {C : Category {ℓ₁} {ℓ′₁}} {D : Category {ℓ₂} {ℓ′₂}} where

  open Iso {ℓ₂} {ℓ′₂} {D}

  iso₁-iso : {F G : Functor C D} {Θ : NatTrans F G} (I : Isomorphism₁ Θ) (x : Category.obj C) → Isomorphism (NatTrans.component Θ x)
  iso₁-iso (makeIso₁ Θ Θ⁻¹ c₁ c₂) x = makeIso (NatTrans.component Θ x) (NatTrans.component Θ⁻¹ x) (c₁ x) (c₂ x)

open iso-to-iso public


≅₁-refl : {ℓ₁ ℓ₂ ℓ′₁ ℓ′₂ : Level} {C : Category {ℓ₁} {ℓ′₁}} {D : Category {ℓ₂} {ℓ′₂}} (F : Functor C D) → F ≅₁ F
≅₁-refl F = make-≅₁ (idNatTrans F) (Iso₁-refl F)

≅₁-sym : {ℓ₁ ℓ₂ ℓ′₁ ℓ′₂ : Level} {C : Category {ℓ₁} {ℓ′₁}} {D : Category {ℓ₂} {ℓ′₂}} {F G : Functor C D} → F ≅₁ G → G ≅₁ F
≅₁-sym (make-≅₁ Θ I) = make-≅₁ (inverse₁ I) (Iso₁-sym I)

≅₁-trans : {ℓ₁ ℓ₂ ℓ′₁ ℓ′₂ : Level} {C : Category {ℓ₁} {ℓ′₁}} {D : Category {ℓ₂} {ℓ′₂}} {F G H : Functor C D} → F ≅₁ G → G ≅₁ H → F ≅₁ H
≅₁-trans (make-≅₁ Θ I) (make-≅₁ Ξ J) = make-≅₁ (Ξ •̂ Θ) (Iso₁-trans J I)


≅₁-⊙-left : {ℓ₁ ℓ₂ ℓ₃ ℓ′₁ ℓ′₂ ℓ′₃ : Level} {C : Category {ℓ₁} {ℓ′₁}} {D : Category {ℓ₂} {ℓ′₂}} {E : Category {ℓ₃} {ℓ′₃}} (G : Functor D E) (F F′ : Functor C D) → F ≅₁ F′ → G ⊙ F ≅₁ G ⊙ F′
≅₁-⊙-left G F F′ (make-≅₁ Θ I) = make-≅₁ (idNatTrans G ⊙̂ Θ) (Iso₁-⊙-left G F F′ I)

≅₁-⊙-right : {ℓ₁ ℓ₂ ℓ₃ ℓ′₁ ℓ′₂ ℓ′₃ : Level} {C : Category {ℓ₁} {ℓ′₁}} {D : Category {ℓ₂} {ℓ′₂}} {E : Category {ℓ₃} {ℓ′₃}} (G G′ : Functor D E) (F : Functor C D) → G ≅₁ G′ → G ⊙ F ≅₁ G′ ⊙ F
≅₁-⊙-right G G′ F (make-≅₁ Θ I) = make-≅₁ (Θ ⊙̂ idNatTrans F) (Iso₁-⊙-right G G′ F I)


