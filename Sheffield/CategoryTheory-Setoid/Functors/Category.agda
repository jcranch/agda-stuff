module Sheffield.CategoryTheory-Setoid.Functors.Category where

open import Data.Product renaming (_×_ to _×′_ ; proj₁ to proj′₁ ; proj₂ to proj′₂)
open import Function.Equality renaming (_∘_ to _∘⁺_ ; id to id⁺)
open import Level
open import Relation.Binary

open import Sheffield.CategoryTheory-Setoid.Categories
open import Sheffield.CategoryTheory-Setoid.Categories.Product
open import Sheffield.CategoryTheory-Setoid.Functors
open import Sheffield.CategoryTheory-Setoid.NaturalTransformations
open import Sheffield.CategoryTheory-Setoid.NaturalTransformations.Equality
open import Sheffield.CategoryTheory-Setoid.NaturalTransformations.Properties
open import Sheffield.CategoryTheory-Setoid.SetoidFunction


Functors : {ℓ₁ ℓ′₁ ℓ″₁ ℓ₂ ℓ′₂ ℓ″₂ : Level} → Category {ℓ₁} {ℓ′₁} {ℓ″₁} → Category {ℓ₂} {ℓ′₂} {ℓ″₂} → Category {ℓ₁ ⊔ ℓ′₁ ⊔ ℓ″₁ ⊔ ℓ₂ ⊔ ℓ′₂ ⊔ ℓ″₂} {ℓ₁ ⊔ ℓ′₁ ⊔ ℓ″₁ ⊔ ℓ₂ ⊔ ℓ′₂ ⊔ ℓ″₂} {ℓ₁ ⊔ ℓ″₂}
Functors C D = makeCat functors nattrans id compose id-l id-r assoc where

  open Category D using (≈-refl ; •-cong)

  functors = Functor C D

  nattrans : functors → functors → Setoid _ _
  nattrans F G = NaturalTransformations {F = F} {G = G}

  id : (F : functors) → Γ (nattrans F F)
  id F = idNatTrans F

  compose : {F G H : functors} → Γ (nattrans G H ⇨ nattrans F G ⇨ nattrans F H)
  compose {F} {G} {H} = record {
    _⟨$⟩_ = λ Φ → record {
      _⟨$⟩_ = λ Ψ → Φ •̂ Ψ ;
      cong = λ {Ψ₁} {Ψ₂} E → make-≈₂ (λ x → •-cong ≈-refl (_≈₂_.component-≈ E x)) } ;
    cong = λ {Φ₁} {Φ₂} E {Ψ₁} {Ψ₂} E′ → make-≈₂ (λ x → •-cong (_≈₂_.component-≈ E x) (_≈₂_.component-≈ E′ x)) }

  id-l : {x y : functors} (f : Γ (nattrans x y)) → Setoid._≈_ (nattrans x y) (compose ⟨$⟩ id y ⟨$⟩ f) f
  id-l Φ = make-≈₂ (λ x → Category.id-l D _)
 
  id-r : {x y : functors} (f : Γ (nattrans x y)) → Setoid._≈_ (nattrans x y) (compose ⟨$⟩ f ⟨$⟩ id x) f
  id-r Φ = make-≈₂ (λ x → Category.id-r D _)

  assoc : {w x y z : functors} (h : Γ (nattrans y z)) (g : Γ (nattrans x y)) (f : Γ (nattrans w x)) → Setoid._≈_ (nattrans w z) (compose ⟨$⟩ (compose ⟨$⟩ h ⟨$⟩ g) ⟨$⟩ f) (compose ⟨$⟩ h ⟨$⟩ (compose ⟨$⟩ g ⟨$⟩ f))
  assoc Θ Ψ Φ = make-≈₂ (λ x → Category.assoc D _ _ _)




constFunctors : {ℓ₁ ℓ′₁ ℓ″₁ ℓ₂ ℓ′₂ ℓ″₂ : Level} (C : Category {ℓ₁} {ℓ′₁} {ℓ″₁}) (D : Category {ℓ₂} {ℓ′₂} {ℓ″₂}) → Functor D (Functors C D)
constFunctors C D = record {
  obj = constFunctor C D ;
  hom = record {
    _⟨$⟩_ = λ f → constNatTrans f ;
    cong = λ z → make-≈₂ (λ _ → z) } ;
  id = λ x → make-≈₂ (λ _ → Setoid.refl (Category.hom D x x)) ;
  compose = λ g f → make-≈₂ (λ x → Setoid.refl (Category.hom D _ _)) }



composition : {ℓ₁ ℓ′₁ ℓ″₁ ℓ₂ ℓ′₂ ℓ″₂ ℓ₃ ℓ′₃ ℓ″₃ : Level} (C : Category {ℓ₁} {ℓ′₁} {ℓ″₁}) (D : Category {ℓ₂} {ℓ′₂} {ℓ″₂}) (E : Category {ℓ₃} {ℓ′₃} {ℓ″₃}) → Functor (Functors D E × Functors C D) (Functors C E)
composition C D E = makeFunctor obj (λ {x} {y} → hom x y) id compose where
  obj : Functor D E ×′ Functor C D → Functor C E
  obj (G , F) = G ⊙ F
  hom : (x y : Category.obj (Functors D E × Functors C D)) → Category.hom (Functors D E × Functors C D) x y ⟶ Category.hom (Functors C E) (obj x) (obj y)
  hom = λ F₁ F₂ → record {
    _⟨$⟩_ = λ x → proj′₁ x ⊙̂ proj′₂ x;
    cong = λ {Φ} {Ψ} e → make-≈₂ (λ x → Category.•-cong E (_≈₂_.component-≈ (proj′₁ e) _) (Functor.hom-cong (proj′₁ F₁) (_≈₂_.component-≈ (proj′₂ e) _))) }
  id : (F : Category.obj (Functors D E × Functors C D)) → hom F F ⟨$⟩ Category.id (Functors D E × Functors C D) F ≈₂ Category.id (Functors C E) (obj F)
  id F = make-≈₂ (λ x → Category.≈-trans E (Category.id-l E _) (Functor.id (proj′₁ F) _))
  compose : {x y z : Category.obj (Functors D E × Functors C D)} (g : Γ (Category.hom (Functors D E × Functors C D) y z)) (f : Γ (Category.hom (Functors D E × Functors C D) x y)) → _
  compose (Φ , Ψ) (Θ , Ω) = make-≈₂ (λ x → Category.≈-sym E (_≈₂_.component-≈ (interchange Φ Θ Ψ Ω) x))



precomposition : {ℓ₁ ℓ′₁ ℓ″₁ ℓ₂ ℓ′₂ ℓ″₂ ℓ₃ ℓ′₃ ℓ″₃ : Level} (C : Category {ℓ₁} {ℓ′₁} {ℓ″₁}) (D : Category {ℓ₂} {ℓ′₂} {ℓ″₂}) (E : Category {ℓ₃} {ℓ′₃} {ℓ″₃}) →
  Functor C D → Functor (Functors D E) (Functors C E)
precomposition C D E F = composition C D E ⊙ (idFunctor (Functors D E) ⋆ constFunctor (Functors D E) (Functors C D) F)

postcomposition : {ℓ₁ ℓ′₁ ℓ″₁ ℓ₂ ℓ′₂ ℓ″₂ ℓ₃ ℓ′₃ ℓ″₃ : Level} (C : Category {ℓ₁} {ℓ′₁} {ℓ″₁}) (D : Category {ℓ₂} {ℓ′₂} {ℓ″₂}) (E : Category {ℓ₃} {ℓ′₃} {ℓ″₃}) →
  Functor D E → Functor (Functors C D) (Functors C E)
postcomposition C D E G = composition C D E ⊙ (constFunctor (Functors C D) (Functors D E) G ⋆ idFunctor (Functors C D))
