module Sheffield.CategoryTheory-Setoid.Categories.Equivalence where

open import Relation.Binary
open import Level

open import Sheffield.CategoryTheory-Setoid.Categories
open import Sheffield.CategoryTheory-Setoid.Functors
open import Sheffield.CategoryTheory-Setoid.Functors.CompositionEqualities
open import Sheffield.CategoryTheory-Setoid.Functors.Isomorphism
open import Sheffield.CategoryTheory-Setoid.Functors.Isomorphism.Properties
open import Sheffield.CategoryTheory-Setoid.NaturalTransformations
open import Sheffield.CategoryTheory-Setoid.NaturalTransformations.Equality
open import Sheffield.CategoryTheory-Setoid.NaturalTransformations.Properties



record Equivalence₀ {ℓ₁ ℓ′₁ ℓ″₁ ℓ₂ ℓ′₂ ℓ″₂ : Level} {C : Category {ℓ₁} {ℓ′₁} {ℓ″₁}} {D : Category {ℓ₂} {ℓ′₂} {ℓ″₂}} (obverse : Functor C D) : Set (ℓ₁ ⊔ ℓ′₁ ⊔ ℓ″₁ ⊔ ℓ₂ ⊔ ℓ′₂ ⊔ ℓ″₂)  where
  constructor make-Equiv₀
  field
    reverse : Functor D C
    unit : reverse ⊙ obverse ≅₁ idFunctor C
    counit : obverse ⊙ reverse ≅₁ idFunctor D



Equivalence₀-refl : {ℓ₁ ℓ′₁ ℓ″₁ : Level} {C : Category {ℓ₁} {ℓ′₁} {ℓ″₁}} → Equivalence₀ (idFunctor C)
Equivalence₀-refl {C = C} = make-Equiv₀ (idFunctor C) (⊙-unital-l _) (⊙-unital-l _)

Equivalence₀-sym : {ℓ₁ ℓ′₁ ℓ″₁ ℓ₂ ℓ′₂ ℓ″₂ : Level} {C : Category {ℓ₁} {ℓ′₁} {ℓ″₁}} {D : Category {ℓ₂} {ℓ′₂} {ℓ″₂}} {F : Functor C D} (e : Equivalence₀ F) → Equivalence₀ (Equivalence₀.reverse e)
Equivalence₀-sym {F = obverse} (make-Equiv₀ reverse unit counit) = make-Equiv₀ obverse counit unit

Equivalence₀-trans : {ℓ₁ ℓ′₁ ℓ″₁ ℓ₂ ℓ′₂ ℓ″₂ ℓ₃ ℓ′₃ ℓ″₃ : Level} {C : Category {ℓ₁} {ℓ′₁} {ℓ″₁}} {D : Category {ℓ₂} {ℓ′₂} {ℓ″₂}} {E : Category {ℓ₃} {ℓ′₃} {ℓ″₃}} {G : Functor D E} {F : Functor C D} → Equivalence₀ G → Equivalence₀ F → Equivalence₀ (G ⊙ F)
Equivalence₀-trans {C = C} {D} {E} {obverse′} {obverse} (make-Equiv₀ reverse′ unit′ counit′) (make-Equiv₀ reverse unit counit) = make-Equiv₀ (reverse ⊙ reverse′) e₁ e₂ where
  e₁ : (reverse ⊙ reverse′) ⊙ (obverse′ ⊙ obverse) ≅₁ idFunctor C
  e₁ = begin
    (reverse ⊙ reverse′) ⊙ (obverse′ ⊙ obverse)
      ≈⟨ ⊙-associative reverse reverse′ (obverse′ ⊙ obverse) ⟩
    reverse ⊙ (reverse′ ⊙ (obverse′ ⊙ obverse))
      ≈⟨ ≅₁-sym (≅₁-cong (≅₁-refl reverse) (⊙-associative reverse′ obverse′ obverse)) ⟩
    reverse ⊙ ((reverse′ ⊙ obverse′) ⊙ obverse)
      ≈⟨ ≅₁-cong (≅₁-refl reverse) (≅₁-cong unit′ (≅₁-refl obverse)) ⟩
    reverse ⊙ (idFunctor D ⊙ obverse)
      ≈⟨ ≅₁-cong (≅₁-refl reverse) (⊙-unital-l obverse) ⟩
    reverse ⊙ obverse
      ≈⟨ unit ⟩
    idFunctor C ∎ where open Functor-reasoning C C
  e₂ : (obverse′ ⊙ obverse) ⊙ (reverse ⊙ reverse′) ≅₁ idFunctor E
  e₂ = begin
    (obverse′ ⊙ obverse) ⊙ (reverse ⊙ reverse′)
      ≈⟨ ⊙-associative obverse′ obverse (reverse ⊙ reverse′) ⟩
    obverse′ ⊙ (obverse ⊙ (reverse ⊙ reverse′))
      ≈⟨ ≅₁-sym (≅₁-cong (≅₁-refl obverse′) (⊙-associative obverse reverse reverse′)) ⟩
    obverse′ ⊙ ((obverse ⊙ reverse) ⊙ reverse′)
      ≈⟨ ≅₁-cong (≅₁-refl obverse′) (≅₁-cong counit (≅₁-refl reverse′)) ⟩
    obverse′ ⊙ (idFunctor D ⊙ reverse′)
      ≈⟨ ≅₁-cong (≅₁-refl obverse′) (⊙-unital-l reverse′) ⟩
    obverse′ ⊙ reverse′
      ≈⟨ counit′ ⟩
    idFunctor E ∎ where open Functor-reasoning E E


infix 4 _≅₀_
record _≅₀_ {ℓ₁ ℓ′₁ ℓ″₁ ℓ₂ ℓ′₂ ℓ″₂ : Level} (C : Category {ℓ₁} {ℓ′₁} {ℓ″₁}) (D : Category {ℓ₂} {ℓ′₂} {ℓ″₂}) : Set (ℓ₁ ⊔ ℓ′₁ ⊔ ℓ″₁ ⊔ ℓ₂ ⊔ ℓ′₂ ⊔ ℓ″₂) where
  constructor make-≅₀
  field
    obverse : Functor C D
    isEquivalence₀ : Equivalence₀ obverse
  open Equivalence₀ isEquivalence₀ public
  reverse-isEquivalence₀ : Equivalence₀ reverse
  reverse-isEquivalence₀ = make-Equiv₀ obverse counit unit


equivalent₀ : {ℓ₁ ℓ′₁ ℓ″₁ ℓ₂ ℓ′₂ ℓ″₂ : Level} {C : Category {ℓ₁} {ℓ′₁} {ℓ″₁}} {D : Category {ℓ₂} {ℓ′₂} {ℓ″₂}} (F : Functor C D) (G : Functor D C) → G ⊙ F ≅₁ idFunctor C → F ⊙ G ≅₁ idFunctor D → C ≅₀ D
equivalent₀ F F⁻¹ unit counit = make-≅₀ F (make-Equiv₀ F⁻¹ unit counit)


≅₀-refl : {ℓ₁ ℓ′₁ ℓ″₁ : Level} {C : Category {ℓ₁} {ℓ′₁} {ℓ″₁}} → C ≅₀ C
≅₀-refl {C = C} = make-≅₀ (idFunctor C) Equivalence₀-refl

≅₀-sym : {ℓ₁ ℓ′₁ ℓ″₁ ℓ₂ ℓ′₂ ℓ″₂ : Level} {C : Category {ℓ₁} {ℓ′₁} {ℓ″₁}} {D : Category {ℓ₂} {ℓ′₂} {ℓ″₂}} → C ≅₀ D → D ≅₀ C
≅₀-sym (make-≅₀ obverse (make-Equiv₀ reverse unit counit)) = make-≅₀ reverse (make-Equiv₀ obverse counit unit)

≅₀-trans : {ℓ₁ ℓ′₁ ℓ″₁ ℓ₂ ℓ′₂ ℓ″₂ ℓ₃ ℓ′₃ ℓ″₃ : Level} {C : Category {ℓ₁} {ℓ′₁} {ℓ″₁}} {D : Category {ℓ₂} {ℓ′₂} {ℓ″₂}} {E : Category {ℓ₃} {ℓ′₃} {ℓ″₃}} → C ≅₀ D → D ≅₀ E → C ≅₀ E
≅₀-trans (make-≅₀ obverse′ ie′) (make-≅₀ obverse ie) = make-≅₀ (obverse ⊙ obverse′) (Equivalence₀-trans ie ie′)


categories : {ℓ₁ ℓ′₁ ℓ″₁ : Level} → Setoid (suc (ℓ₁ ⊔ ℓ′₁ ⊔ ℓ″₁)) (ℓ₁ ⊔ ℓ′₁ ⊔ ℓ″₁)
categories {ℓ₁} {ℓ′₁} {ℓ″₁} = record {
  Carrier = Category {ℓ₁} {ℓ′₁} {ℓ″₁};
  _≈_ = _≅₀_;
  isEquivalence = record {
    refl = ≅₀-refl;
    sym = ≅₀-sym;
    trans = ≅₀-trans } }