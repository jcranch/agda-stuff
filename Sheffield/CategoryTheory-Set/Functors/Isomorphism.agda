module Sheffield.CategoryTheory-Set.Functors.Isomorphism where

open import Level
import Relation.Binary.EqReasoning
open import Relation.Binary.PropositionalEquality

open import Sheffield.CategoryTheory-Set.Categories
open import Sheffield.CategoryTheory-Set.Functors
open import Sheffield.CategoryTheory-Set.NaturalTransformations
open import Sheffield.CategoryTheory-Set.NaturalTransformations.Equality
open import Sheffield.CategoryTheory-Set.NaturalTransformations.Properties


-- still to do: uniqueness of inverses


record Isomorphism₁ {ℓ₁ ℓ₂ ℓ′₁ ℓ′₂ : Level} {C : Category {ℓ₁} {ℓ′₁}} {D : Category {ℓ₂} {ℓ′₂}} {F G : Functor C D} (Θ : NatTrans F G) : Set (ℓ₁ ⊔ ℓ₂ ⊔ ℓ′₁ ⊔ ℓ′₂)  where
  constructor make-Iso₁
  field
    inverse : NatTrans G F
    unit : inverse •̂ Θ ≡₂ idNatTrans F
    counit : Θ •̂ inverse ≡₂ idNatTrans G


infix 4 _≅₁_
record _≅₁_ {ℓ₁ ℓ₂ ℓ′₁ ℓ′₂ : Level} {C : Category {ℓ₁} {ℓ′₁}} {D : Category {ℓ₂} {ℓ′₂}} (F G : Functor C D) : Set (ℓ₁ ⊔ ℓ₂ ⊔ ℓ′₁ ⊔ ℓ′₂) where
  constructor make-≅₁
  field
    obverse : NatTrans F G
    isIsomorphism₁ : Isomorphism₁ obverse
  open Isomorphism₁ isIsomorphism₁ public


isomorphic₁ : {ℓ₁ ℓ₂ ℓ′₁ ℓ′₂ : Level} {C : Category {ℓ₁} {ℓ′₁}} {D : Category {ℓ₂} {ℓ′₂}} {F G : Functor C D} (Θ : NatTrans F G) (Θ⁻¹ : NatTrans G F) → Θ⁻¹ •̂ Θ ≡₂ idNatTrans F → Θ •̂ Θ⁻¹ ≡₂ idNatTrans G → F ≅₁ G
isomorphic₁ Θ Θ⁻¹ unit counit = make-≅₁ Θ (make-Iso₁ Θ⁻¹ unit counit)



≅₁-to-NatTrans : {ℓ₁ ℓ₂ ℓ′₁ ℓ′₂ : Level} {C : Category {ℓ₁} {ℓ′₁}} {D : Category {ℓ₂} {ℓ′₂}} {F G : Functor C D} → F ≅₁ G → NatTrans F G
≅₁-to-NatTrans (make-≅₁ Θ _) = Θ
≅₁-to-NatTrans⁻¹ : {ℓ₁ ℓ₂ ℓ′₁ ℓ′₂ : Level} {C : Category {ℓ₁} {ℓ′₁}} {D : Category {ℓ₂} {ℓ′₂}} {F G : Functor C D} → F ≅₁ G → NatTrans G F
≅₁-to-NatTrans⁻¹ (make-≅₁ Θ (make-Iso₁ Θ⁻¹ _ _)) = Θ⁻¹


inverse₁ : {ℓ₁ ℓ₂ ℓ′₁ ℓ′₂ : Level} {C : Category {ℓ₁} {ℓ′₁}} {D : Category {ℓ₂} {ℓ′₂}} {F G : Functor C D} {Θ : NatTrans F G} → Isomorphism₁ Θ → NatTrans G F
inverse₁ (make-Iso₁ Θ⁻¹ _ _) = Θ⁻¹


Iso₁-refl : {ℓ₁ ℓ₂ ℓ′₁ ℓ′₂ : Level} {C : Category {ℓ₁} {ℓ′₁}} {D : Category {ℓ₂} {ℓ′₂}} (F : Functor C D) → Isomorphism₁ (idNatTrans F)
Iso₁-refl F = make-Iso₁ (idNatTrans F) (•̂-unit-l (idNatTrans F)) (•̂-unit-l (idNatTrans F))

Iso₁-sym : {ℓ₁ ℓ₂ ℓ′₁ ℓ′₂ : Level} {C : Category {ℓ₁} {ℓ′₁}} {D : Category {ℓ₂} {ℓ′₂}} {F G : Functor C D} {Θ : NatTrans F G} (I : Isomorphism₁ Θ) → Isomorphism₁ (inverse₁ I)
Iso₁-sym {Θ = Θ} (make-Iso₁ Θ⁻¹ c₁ c₂) = make-Iso₁ Θ c₂ c₁

Iso₁-trans : {ℓ₁ ℓ₂ ℓ′₁ ℓ′₂ : Level} {C : Category {ℓ₁} {ℓ′₁}} {D : Category {ℓ₂} {ℓ′₂}} {F G H : Functor C D} {Ξ : NatTrans G H} {Θ : NatTrans F G} (IΞ : Isomorphism₁ Ξ) (IΘ : Isomorphism₁ Θ) → Isomorphism₁ (Ξ •̂ Θ)
Iso₁-trans {_} {ℓ₂} {_} {ℓ′₂} {_} {D} (make-Iso₁ Ξ⁻¹ c₁ c₂) (make-Iso₁ Θ⁻¹ c₃ c₄) = make-Iso₁ (Θ⁻¹ •̂ Ξ⁻¹) (λ x → double-cancellation (c₃ x) (c₁ x)) (λ x → double-cancellation (c₂ x) (c₄ x)) where
  open Iso D


Iso₁-⊙-left : {ℓ₁ ℓ₂ ℓ₃ ℓ′₁ ℓ′₂ ℓ′₃ : Level} {C : Category {ℓ₁} {ℓ′₁}} {D : Category {ℓ₂} {ℓ′₂}} {E : Category {ℓ₃} {ℓ′₃}} (G : Functor D E) (F F′ : Functor C D) {Θ : NatTrans F F′} (I : Isomorphism₁ Θ) → Isomorphism₁ (idNatTrans G ⊙̂ Θ)
Iso₁-⊙-left G F F′ {Θ = Θ} (make-Iso₁ Θ⁻¹ c₁ c₂) = make-Iso₁ (idNatTrans G ⊙̂ Θ⁻¹) e₁ e₂ where
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
Iso₁-⊙-right G G′ F {Θ = Θ} (make-Iso₁ Θ⁻¹ c₁ c₂) = make-Iso₁ (Θ⁻¹ ⊙̂ idNatTrans F) e₁ e₂ where
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

  open Iso D

  iso₁-iso : {F G : Functor C D} {Θ : NatTrans F G} (I : Isomorphism₁ Θ) (x : Category.obj C) → Isomorphism (NatTrans.component Θ x)
  iso₁-iso {Θ = Θ} (make-Iso₁ Θ⁻¹ c₁ c₂) x = makeIso (NatTrans.component Θ x) (NatTrans.component Θ⁻¹ x) (c₁ x) (c₂ x)

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


const-≅₁-l : {ℓ₁ ℓ′₁ ℓ₂ ℓ′₂ ℓ₃ ℓ′₃ : Level}
  {C : Category {ℓ₁} {ℓ′₁}} {D : Category {ℓ₂} {ℓ′₂}} {E : Category {ℓ₃} {ℓ′₃}}
  (F : Functor C D) (x : Category.obj E) → constFunctor D E x ⊙ F ≅₁ constFunctor C E x
const-≅₁-l {C = C} {D = D} {E = E} (makeFunctor obj hom id compose) x = make-≅₁ Θ (make-Iso₁ Θ⁻¹ (λ _ → Category.id-l E (Category.id E x)) (λ _ → Category.id-l E (Category.id E x))) where
  Θ : NatTrans (constFunctor D E x ⊙ makeFunctor obj hom id compose) (constFunctor C E x)
  Θ = makeNatTrans (λ _ → Category.id E x) (λ _ → refl)
  Θ⁻¹ : NatTrans (constFunctor C E x) (constFunctor D E x ⊙ makeFunctor obj hom id compose)
  Θ⁻¹ = makeNatTrans (λ _ → Category.id E x) (λ _ → refl)

const-≅₁-r : {ℓ₁ ℓ′₁ ℓ₂ ℓ′₂ ℓ₃ ℓ′₃ : Level}
  {C : Category {ℓ₁} {ℓ′₁}} {D : Category {ℓ₂} {ℓ′₂}} {E : Category {ℓ₃} {ℓ′₃}}
  (F : Functor D E) (x : Category.obj D) → F ⊙ constFunctor C D x ≅₁ constFunctor C E (Functor.obj F x)
const-≅₁-r {C = C} {D = D} {E = E} (makeFunctor obj hom id compose) x = make-≅₁ Θ (make-Iso₁ Θ⁻¹ (λ _ → Category.id-l E (Category.id E (obj x))) (λ _ → Category.id-l E (Category.id E (obj x)))) where
  Θ : NatTrans (makeFunctor obj hom id compose ⊙ constFunctor C D x) (constFunctor C E (obj x))
  Θ = makeNatTrans (λ _ → Category.id E (obj x)) (λ _ → cong (Category.compose E (Category.id E (obj x))) (id x))
  Θ⁻¹ : NatTrans (constFunctor C E (obj x)) (makeFunctor obj hom id compose ⊙ constFunctor C D x)
  Θ⁻¹ = makeNatTrans (λ _ → Category.id E (obj x)) (λ _ → cong (λ α → Category.compose E α (Category.id E (obj x))) (sym (id x)))