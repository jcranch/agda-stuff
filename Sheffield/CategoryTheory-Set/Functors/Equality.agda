module Sheffield.CategoryTheory-Set.Functors.Equality where

open import Level
open import Relation.Binary
open import Relation.Binary.PropositionalEquality
open ≡-Reasoning

open import Sheffield.CategoryTheory-Set.Categories
open import Sheffield.CategoryTheory-Set.Functors
open import Sheffield.CategoryTheory-Set.Functors.Isomorphism
open import Sheffield.CategoryTheory-Set.ExtensionalEquality
open import Sheffield.CategoryTheory-Set.NaturalTransformations



infix 4 _≡₁_
record _≡₁_ {ℓ₁ ℓ₂ ℓ′₁ ℓ′₂ : Level}
       {C : Category {ℓ₁} {ℓ′₁}} {D : Category {ℓ₂} {ℓ′₂}}
       (F : Functor C D) (G : Functor C D) : Set (ℓ₁ ⊔ ℓ₂ ⊔ ℓ′₁ ⊔ ℓ′₂) where
  constructor refl₁
  field
    obj : (x : Category.obj C) → Functor.obj F x ≡ Functor.obj G x
    hom : {x : Category.obj C} {y : Category.obj C} (f : Category.hom C x y) → subst₂ (Category.hom D) (obj x) (obj y) (Functor.hom F f) ≡ Functor.hom G f



private
  ≡-subst-sym : {i j : Level} {A : Set i} {P : A → Set j} {a₁ a₂ : A} {x₁ : P a₁} {x₂ : P a₂} {e : a₁ ≡ a₂} → subst P e x₁ ≡ x₂ → subst P (sym e) x₂ ≡ x₁
  ≡-subst-sym {i} {j} {A} {P} {a} {.a} {x} {.x} {refl} refl = refl

  ≡-subst₂-sym : {i j k : Level} {A : Set i} {B : Set j} (P : A → B → Set k) {a₁ a₂ : A} {b₁ b₂ : B} {x₁ : P a₁ b₁} {x₂ : P a₂ b₂} (e : a₁ ≡ a₂) (f : b₁ ≡ b₂) → subst₂ P e f x₁ ≡ x₂ → subst₂ P (sym e) (sym f) x₂ ≡ x₁
  ≡-subst₂-sym {i} {j} {k} {A} {B} P {a} {.a} {b} {.b} {x} {.x} refl refl refl = refl

  ≡-subst-trans : {i j : Level} {A : Set i} {P : A → Set j} {a₁ a₂ a₃ : A} {x₁ : P a₁} {x₂ : P a₂} {x₃ : P a₃} {e : a₁ ≡ a₂} {e′ : a₂ ≡ a₃} → subst P e x₁ ≡ x₂ → subst P e′ x₂ ≡ x₃ → subst P (trans e e′) x₁ ≡ x₃
  ≡-subst-trans {i} {j} {A} {P} {a} {.a} {.a} {x₁} {x₂} {.x₂} {refl} {refl} E refl = E

  ≡-subst₂-trans : {i j k : Level} {A : Set i} {B : Set j} (P : A → B → Set k) {a₁ a₂ a₃ : A} {b₁ b₂ b₃ : B} {x₁ : P a₁ b₁} {x₂ : P a₂ b₂} {x₃ : P a₃ b₃} (e : a₁ ≡ a₂) (e′ : a₂ ≡ a₃) (f : b₁ ≡ b₂) (f′ : b₂ ≡ b₃) → subst₂ P e f x₁ ≡ x₂ → subst₂ P e′ f′ x₂ ≡ x₃ → subst₂ P (trans e e′) (trans f f′) x₁ ≡ x₃
  ≡-subst₂-trans {i} {j} {k} {A} {B} P {a} {.a} {.a} {b} {.b} {.b} {x₁} {x₂} {.x₂} refl refl refl refl E refl = E



≡₁-refl : {ℓ₁ ℓ₂ ℓ′₁ ℓ′₂ : Level}
          {C : Category {ℓ₁} {ℓ′₁}} {D : Category {ℓ₂} {ℓ′₂}}
          (F : Functor C D) → F ≡₁ F
≡₁-refl F = refl₁ (λ x → refl) (λ f → refl)

≡₁-sym : {ℓ₁ ℓ₂ ℓ′₁ ℓ′₂ : Level}
         {C : Category {ℓ₁} {ℓ′₁}} {D : Category {ℓ₂} {ℓ′₂}}
         {F G : Functor C D} → F ≡₁ G → G ≡₁ F
≡₁-sym {C = C} {D = D} (refl₁ α β) = refl₁ (λ x → sym (α x)) (λ {x} {y} f → ≡-subst₂-sym (Category.hom D) (α x) (α y) (β f))

≡₁-trans : {ℓ₁ ℓ₂ ℓ′₁ ℓ′₂ : Level}
           {C : Category {ℓ₁} {ℓ′₁}} {D : Category {ℓ₂} {ℓ′₂}}
           {F G H : Functor C D} → F ≡₁ G → G ≡₁ H → F ≡₁ H
≡₁-trans {C = C} {D = D} (refl₁ α β) (refl₁ α′ β′) = refl₁ (λ x → trans (α x) (α′ x)) (λ {x} {y} f → ≡-subst₂-trans (Category.hom D) (α x) (α′ x) (α y) (α′ y) (β f) (β′ f))


const-≡₁-l : {ℓ₁ ℓ′₁ ℓ₂ ℓ′₂ ℓ₃ ℓ′₃ : Level}
  {C : Category {ℓ₁} {ℓ′₁}} {D : Category {ℓ₂} {ℓ′₂}} {E : Category {ℓ₃} {ℓ′₃}}
  (F : Functor C D) (x : Category.obj E) → constFunctor D E x ⊙ F ≡₁ constFunctor C E x
const-≡₁-l (makeFunctor obj hom id compose) x = refl₁ (λ _ → refl) (λ _ → refl)

const-≡₁-r : {ℓ₁ ℓ′₁ ℓ₂ ℓ′₂ ℓ₃ ℓ′₃ : Level}
  {C : Category {ℓ₁} {ℓ′₁}} {D : Category {ℓ₂} {ℓ′₂}} {E : Category {ℓ₃} {ℓ′₃}}
  (F : Functor D E) (x : Category.obj D) → F ⊙ constFunctor C D x ≡₁ constFunctor C E (Functor.obj F x)
const-≡₁-r (makeFunctor obj hom id compose) x = refl₁ (λ _ → refl) (λ _ → id x)

{-
≡₁-to-≅₁ : {ℓ₁ ℓ₂ ℓ′₁ ℓ′₂ : Level}
  {C : Category {ℓ₁} {ℓ′₁}} {D : Category {ℓ₂} {ℓ′₂}}
  {F : Functor C D} {G : Functor C D} → F ≡₁ G → F ≅₁ G
≡₁-to-≅₁ {C = C} {D = D} {F = F} {G = G} (refl₁ ≡₁-obj ≡₁-hom) = make-≅₁ Θ {!iso!} where
  open Category C renaming (obj to obj′ ; hom to hom′ ; id to id′ ; _•_ to _•′_)
  open Category D
  F₀ = Functor.obj F
  F₁ = λ {x} {y} f → Functor.hom F {x} {y} f
  G₀ = Functor.obj G
  G₁ = λ {x} {y} f → Functor.hom G {x} {y} f
  Θ : NatTrans F G
  Θ = makeNatTrans component naturality where
    component : (x : obj′) → hom (F₀ x) (G₀ x)
    component x = subst (λ α → hom (F₀ x) α) (≡₁-obj x) (id (F₀ x))
    naturality : {x y : obj′} (f : hom′ x y) → component y • F₁ f ≡ G₁ f • component x
    naturality {x} {y} f = begin
      subst (hom (F₀ y)) (≡₁-obj y) (id (F₀ y)) • F₁ f
        ≡⟨ {!!} ⟩
      subst (hom (F₀ x)) (≡₁-obj y) (F₁ f)
        ≡⟨ {!≡₁-hom f!} ⟩
      subst (λ x′ → hom x′ (G₀ y)) (sym (≡₁-obj x)) (G₁ f)
        ≡⟨ {!!} ⟩
      G₁ f • subst (hom (F₀ x)) (≡₁-obj x) (id (F₀ x)) ∎
-}