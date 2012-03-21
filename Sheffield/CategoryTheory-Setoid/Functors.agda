module Sheffield.CategoryTheory-Setoid.Functors where

open import Function.Injection hiding (id ; _∘_)
open import Function.Surjection hiding (id ; _∘_)
open import Function hiding (id ; const)
open import Function.Equality renaming (_∘_ to _∘⁺_ ; id to id⁺)
open import Level
open import Relation.Binary


open import Sheffield.CategoryTheory-Setoid.Categories
open import Sheffield.CategoryTheory-Setoid.SetoidFunction renaming (flip to flip′)


record Functor {ℓ₁ ℓ′₁ ℓ″₁ ℓ₂ ℓ′₂ ℓ″₂ : Level} (C : Category {ℓ₁} {ℓ′₁} {ℓ″₁}) (D : Category {ℓ₂} {ℓ′₂} {ℓ″₂}) : Set (ℓ₁ ⊔ ℓ′₁ ⊔ ℓ″₁ ⊔ ℓ₂ ⊔ ℓ′₂ ⊔ ℓ″₂) where
  constructor makeFunctor

  open Category C hiding (obj ; hom ; id ; compose) renaming (_≈_ to _≈′_ ; _•_ to _•′_ ; ≈-sym to ≈′-sym ; ≈-trans to ≈′-trans)
  open Category D hiding (obj ; hom ; id ; compose)

  field
    obj : Category.obj C → Category.obj D
    hom : {x y : Category.obj C} → Category.hom C x y ⟶ Category.hom D (obj x) (obj y)
    id : (x : Category.obj C) → hom ⟨$⟩ Category.id C x ≈ Category.id D (obj x)
    compose : {x y z : Category.obj C} (g : Γ (Category.hom C y z)) (f : Γ (Category.hom C x y)) → hom ⟨$⟩ (g •′ f) ≈ (hom ⟨$⟩ g) • (hom ⟨$⟩ f)

  homsets : {x y : Category.obj C} → Category.homset C x y → Category.homset D (obj x) (obj y)
  homsets = _⟨$⟩_ hom

  hom-cong : {x y : Category.obj C} {f g : Category.homset C x y} → f ≈′ g → hom ⟨$⟩ f ≈ hom ⟨$⟩ g
  hom-cong = cong hom

  isos : {x y : Category.obj C} {f : Category.homset C x y} → Iso.Isomorphism C f → Iso.Isomorphism D (homsets f)
  isos {x} {y} {f} (Iso.makeIso f⁻¹ unit counit) = Iso.makeIso (homsets f⁻¹) (≈-trans (≈-sym (compose f⁻¹ f)) (≈-trans (hom-cong unit) (id x))) (≈-trans (≈-sym (compose f f⁻¹)) (≈-trans (hom-cong counit) (id y)))

  on-≅ : {x y : Category.obj C} → Iso._≅_ C x y → Iso._≅_ D (Functor.obj x) (Functor.obj y)
  on-≅ (Iso.make-≅ f i) = Iso.make-≅ (homsets f) (isos i)



idFunctor : {ℓ₁ ℓ′₁ ℓ″₁ : Level} (C : Category {ℓ₁} {ℓ′₁} {ℓ″₁}) → Functor C C
idFunctor C = makeFunctor (λ z → z) id⁺ (λ x → Setoid.refl (Category.hom C x x)) (λ g f → Setoid.refl (Category.hom C _ _))

constFunctor : {ℓ₁ ℓ′₁ ℓ″₁ ℓ₂ ℓ′₂ ℓ″₂ : Level} (C : Category {ℓ₁} {ℓ′₁} {ℓ″₁}) (D : Category {ℓ₂} {ℓ′₂} {ℓ″₂}) → Category.obj D → Functor C D
constFunctor C D x = makeFunctor (λ _ → x) (const (Category.id D x)) (λ _ → Setoid.refl (Category.hom D x x)) (λ _ _ → Setoid.sym (Category.hom D x x) ((Category.id-l D (Category.id D x))))



module functor-composition {ℓ₁ ℓ′₁ ℓ″₁ ℓ₂ ℓ′₂ ℓ″₂ ℓ₃ ℓ′₃ ℓ″₃ : Level} {C : Category {ℓ₁} {ℓ′₁} {ℓ″₁}} {D : Category {ℓ₂} {ℓ′₂} {ℓ″₂}} {E : Category {ℓ₃} {ℓ′₃} {ℓ″₃}} where
  open Category C renaming (obj to obC ; hom to homC)
  open Category D renaming (id to id′ ; _•_ to _•′_ ; _≈_ to _≈′_)
  open Category E renaming (id to id″ ; _•_ to _•″_ ; _≈_ to _≈″_)

  infixr 7 _⊙_
  _⊙_ : Functor D E → Functor C D → Functor C E
  makeFunctor G₀ G₁ G-id G-compose ⊙ makeFunctor F₀ F₁ F-id F-compose = makeFunctor (G₀ ∘ F₀) (G₁ ∘⁺ F₁) ⊙-id ⊙-compose where

    ⊙-id : (x : obC) → G₁ ∘⁺ F₁ ⟨$⟩ id x ≈″ id″ (G₀ (F₀ x))
    ⊙-id x = begin
      G₁ ∘⁺ F₁ ⟨$⟩ id x
        ≈⟨ cong G₁ (F-id x) ⟩
      G₁ ⟨$⟩ id′ (F₀ x)
        ≈⟨ G-id (F₀ x) ⟩
      id″ (G₀ (F₀ x)) ∎ where open Category.≈-Reasoning E _ _

    ⊙-compose : {x y z : obC} (g : Γ (homC y z)) (f : Γ (homC x y)) → (G₁ ∘⁺ F₁) ⟨$⟩ (g • f) ≈″ ((G₁ ∘⁺ F₁) ⟨$⟩ g) •″ ((G₁ ∘⁺ F₁) ⟨$⟩ f)
    ⊙-compose {x} {y} {z} g f = begin
      (G₁ ∘⁺ F₁) ⟨$⟩ (g • f)
        ≈⟨ cong G₁ (F-compose g f) ⟩
      G₁ ⟨$⟩ (F₁ ⟨$⟩ g) •′ (F₁ ⟨$⟩ f)
        ≈⟨ G-compose (F₁ ⟨$⟩ g) (F₁ ⟨$⟩ f) ⟩
      ((G₁ ∘⁺ F₁) ⟨$⟩ g) •″ ((G₁ ∘⁺ F₁) ⟨$⟩ f) ∎ where open Category.≈-Reasoning E _ _

open functor-composition public




functor-op : {ℓ₁ ℓ′₁ ℓ″₁ ℓ₂ ℓ′₂ ℓ″₂ : Level} {C : Category {ℓ₁} {ℓ′₁} {ℓ″₁}} {D : Category {ℓ₂} {ℓ′₂} {ℓ″₂}} → Functor C D → Functor (opposite C) (opposite D)
functor-op (makeFunctor obj hom id compose) = makeFunctor obj hom id (flip compose)



faithful : {ℓ₁ ℓ′₁ ℓ″₁ ℓ₂ ℓ′₂ ℓ″₂ : Level} {C : Category {ℓ₁} {ℓ′₁} {ℓ″₁}} {D : Category {ℓ₂} {ℓ′₂} {ℓ″₂}} (F : Functor C D) → Set _
faithful {C = C} F = (x y : Category.obj C) → Injective (Functor.hom F {x} {y})


full : {ℓ₁ ℓ′₁ ℓ″₁ ℓ₂ ℓ′₂ ℓ″₂ : Level} {C : Category {ℓ₁} {ℓ′₁} {ℓ″₁}} {D : Category {ℓ₂} {ℓ′₂} {ℓ″₂}} (F : Functor C D) → Set _
full {C = C} F = (x y : Category.obj C) → Surjective (Functor.hom F {x} {y})



on-classes : {ℓ₁ ℓ′₁ ℓ″₁ ℓ₂ ℓ′₂ ℓ″₂ : Level} {C : Category {ℓ₁} {ℓ′₁} {ℓ″₁}} {D : Category {ℓ₂} {ℓ′₂} {ℓ″₂}} → Functor C D → Iso.classes C ⟶ Iso.classes D
on-classes F = record {
  _⟨$⟩_ = Functor.obj F ;
  cong = Functor.on-≅ F }


essentially-surjective : {ℓ₁ ℓ′₁ ℓ″₁ ℓ₂ ℓ′₂ ℓ″₂ : Level} {C : Category {ℓ₁} {ℓ′₁} {ℓ″₁}} {D : Category {ℓ₂} {ℓ′₂} {ℓ″₂}} → Functor C D → Set _
essentially-surjective F = Surjective (on-classes F)



full-subcategory-inclusion : {ℓ ℓ′ ℓ″ ℓ⁺ : Level} (C : Category {ℓ} {ℓ′} {ℓ″}) {O : Set ℓ⁺} (f : O → Category.obj C) → Functor (full-subcategory C f) C
full-subcategory-inclusion C f = record {
  obj = f ;
  hom = λ {x} {y} → id⁺ ;
  id = λ _ → Category.≈-refl C ;
  compose = λ _ _ → Category.≈-refl C }
