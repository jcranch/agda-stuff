module Sheffield.CategoryTheory-Setoid.Comma where

open import Data.Product
open import Function using (flip ; _∘_)
open import Function.Equality hiding (id ; _⟶_ ; _∘_) renaming (_⇨_ to _⟶_)
open import Level
open import Relation.Binary

open import Sheffield.CategoryTheory-Setoid.Categories
open import Sheffield.CategoryTheory-Setoid.Functors
open import Sheffield.CategoryTheory-Setoid.NaturalTransformations
open import Sheffield.CategoryTheory-Setoid.SetoidFunction



module comma-category {ℓ₁ ℓ′₁ ℓ″₁ ℓ₂ ℓ′₂ ℓ″₂ ℓ₃ ℓ′₃ ℓ″₃ : Level} {A : Category {ℓ₁} {ℓ′₁} {ℓ″₁}} {B : Category {ℓ₂} {ℓ′₂} {ℓ″₂}} {C : Category {ℓ₃} {ℓ′₃} {ℓ″₃}} (F : Functor A C) (G : Functor B C) where

  open Category A hiding (module ≈-Reasoning) renaming (obj to obj₁ ; hom to hom₁ ; homset to homset₁ ; id to id₁ ; id-l to id-l₁ ; id-r to id-r₁ ; assoc to assoc₁ ; compose to compose₁ ; _•_ to _•ˡ_ ; _≈_ to _≈ˡ_ ; ≈-refl to ≈ˡ-refl ; ≈-sym to ≈ˡ-sym ; ≈-trans to ≈ˡ-trans ; •-cong to •ˡ-cong)
  open Category B hiding (module ≈-Reasoning) renaming (obj to obj₂ ; hom to hom₂ ; homset to homset₂ ; id to id₂ ; id-l to id-l₂ ; id-r to id-r₂ ; assoc to assoc₂ ; compose to compose₂ ; _•_ to _•ʳ_ ; _≈_ to _≈ʳ_ ; ≈-refl to ≈ʳ-refl ; ≈-sym to ≈ʳ-sym ; ≈-trans to ≈ʳ-trans ; •-cong to •ʳ-cong)
  open Category C renaming (obj to obj₀ ; hom to hom₀ ; homset to homset₀ ; id to id₀ ; id-l to id-l₀ ; id-r to id-r₀ ; assoc to assoc₀ ; compose to compose₀)

  open Functor F hiding (hom) renaming (obj to F₀ ; homsets to F₁ ; id to idF ; compose to composeF)
  open Functor G hiding (hom) renaming (obj to G₀ ; homsets to G₁ ; id to idG ; compose to composeG)

  module comma-structure where

    record Comma-obj : Set (ℓ₁ ⊔ ℓ₂ ⊔ ℓ′₃) where
      constructor [_,_,_]

      field
        s : obj₁
        t : obj₂
        f : homset₀ (F₀ s) (G₀ t)

    record Comma-homset (X₁ : Comma-obj) (X₂ : Comma-obj) : Set (ℓ′₁ ⊔ ℓ′₂ ⊔ ℓ″₃) where
      constructor make-hom

      s₁ = Comma-obj.s X₁
      t₁ = Comma-obj.t X₁
      f₁ = Comma-obj.f X₁
      s₂ = Comma-obj.s X₂
      t₂ = Comma-obj.t X₂
      f₂ = Comma-obj.f X₂

      field
        mor₁  : homset₁ s₁ s₂
        mor₂  : homset₂ t₁ t₂
        eq  : G₁ mor₂ • f₁ ≈ f₂ • F₁ mor₁

    infix 4 _≈′_
    _≈′_ : {X : Comma-obj} {Y : Comma-obj} → Rel (Comma-homset X Y) (ℓ″₁ ⊔ ℓ″₂)
    _≈′_ (make-hom mor₁ mor₂ eq) (make-hom mor₁' mor₂' eq') = (mor₁ ≈ˡ mor₁') × (mor₂ ≈ʳ mor₂')

    Comma-hom : (X : Comma-obj) (Y : Comma-obj) → Setoid (ℓ′₁ ⊔ ℓ′₂ ⊔ ℓ″₃) (ℓ″₁ ⊔ ℓ″₂)
    Comma-hom X Y = record {
      Carrier = Comma-homset X Y ;
      _≈_ = _≈′_ ;
      isEquivalence = record {
        refl = ≈ˡ-refl , ≈ʳ-refl ;
        sym = λ x → ≈ˡ-sym (proj₁ x) , ≈ʳ-sym (proj₂ x) ;
        trans = λ x y → ≈ˡ-trans (proj₁ x) (proj₁ y) , ≈ʳ-trans (proj₂ x) (proj₂ y) } }

    Comma-id : (x : Comma-obj) → Comma-homset x x
    Comma-id [ s , t , f ] = make-hom (id₁ s) (id₂ t) e where
      open ≈-Reasoning _ _
      e = begin
        G₁ (id₂ t) • f
          ≈⟨ •-cong (idG t) ≈-refl ⟩
        id₀ (G₀ t) • f
          ≈⟨ id-l₀ f ⟩
        f
          ≈⟨ ≈-sym (id-r₀ f) ⟩
        f • id₀ (F₀ s)
          ≈⟨ •-cong ≈-refl (≈-sym (idF s)) ⟩
        f • F₁ (id₁ s) ∎

    infix 7 _•′_
    _•′_ : {x y z : Comma-obj} → Comma-homset y z → Comma-homset x y → Comma-homset x z
    _•′_ {[ s₁ , t₁ , f₁ ]} {[ s₂ , t₂ , f₂ ]} {[ s₃ , t₃ , f₃ ]} (make-hom g′ h′ e′) (make-hom g h e) = make-hom (g′ •ˡ g) (h′ •ʳ h) e″ where
      open ≈-Reasoning _ _
      e″ = begin
        G₁ (h′ •ʳ h) • f₁
          ≈⟨ •-cong (Functor.compose G h′ h) ≈-refl ⟩
        (G₁ h′ • G₁ h) • f₁
          ≈⟨ assoc₀ (G₁ h′) (G₁ h) f₁ ⟩
        G₁ h′ • (G₁ h • f₁)
          ≈⟨ •-cong ≈-refl e ⟩
        G₁ h′ • (f₂ • F₁ g)
          ≈⟨ ≈-sym (assoc₀ (G₁ h′) f₂ (F₁ g)) ⟩
        (G₁ h′ • f₂) • F₁ g
          ≈⟨ •-cong e′ ≈-refl ⟩
        (f₃ • F₁ g′) • F₁ g
          ≈⟨ assoc₀ f₃ (F₁ g′) (F₁ g) ⟩
        f₃ • (F₁ g′ • F₁ g)
          ≈⟨ •-cong ≈-refl (≈-sym (Functor.compose F g′ g)) ⟩
        f₃ • F₁ (g′ •ˡ g) ∎

    Comma-compose : {x y z : Comma-obj} → Γ (Comma-hom y z ⟶ Comma-hom x y ⟶ Comma-hom x z)
    Comma-compose {[ s₁ , t₁ , f₁ ]} {[ s₂ , t₂ , f₂ ]} {[ s₃ , t₃ , f₃ ]} = record {
      _⟨$⟩_ = λ β → record {
        _⟨$⟩_ = λ α → β •′ α ;
        cong = λ e → •ˡ-cong ≈ˡ-refl (proj₁ e) , •ʳ-cong ≈ʳ-refl (proj₂ e) } ;
      cong = λ e′ e → •ˡ-cong (proj₁ e′) (proj₁ e) , •ʳ-cong (proj₂ e′) (proj₂ e) }

    id-l : {x y : Comma-obj} (f : Comma-homset x y) → Comma-id y •′ f ≈′ f
    id-l (make-hom g h e) = id-l₁ g , id-l₂ h

    id-r : {x y : Comma-obj} (f : Comma-homset x y) → f •′ Comma-id x ≈′ f
    id-r (make-hom g h e) = id-r₁ g , id-r₂ h

    assoc : {w x y z : Comma-obj} (h : Comma-homset y z) (g : Comma-homset x y) (f : Comma-homset w x) → (h •′ g) •′ f ≈′ h •′ (g •′ f)
    assoc (make-hom g″ f″ e″) (make-hom g′ f′ e′) (make-hom g f e) = assoc₁ g″ g′ g , assoc₂ f″ f′ f

  open comma-structure

  Comma : Category {ℓ₁ ⊔ ℓ₂ ⊔ ℓ′₃} {ℓ′₁ ⊔ ℓ′₂ ⊔ ℓ″₃} {ℓ″₁ ⊔ ℓ″₂}
  Comma = makeCat Comma-obj Comma-hom Comma-id Comma-compose id-l id-r assoc

  Proj₁ : Functor Comma A
  Proj₁ = record {
    obj = Comma-obj.s ;
    hom = record {
      _⟨$⟩_ = Comma-homset.mor₁ ;
      cong = proj₁ } ;
    id = λ x → ≈ˡ-refl ;
    compose = λ g f → ≈ˡ-refl }

  Proj₂ : Functor Comma B
  Proj₂ = record {
    obj = Comma-obj.t ;
    hom = record {
      _⟨$⟩_ = Comma-homset.mor₂ ;
      cong = proj₂ } ;
    id = λ x → ≈ʳ-refl ;
    compose = λ g f → ≈ʳ-refl }

  -- the fundamental natural transformation
  Proj₁₂ : NatTrans (F ⊙ Proj₁) (G ⊙ Proj₂)
  Proj₁₂ = makeNatTrans Comma-obj.f (≈-sym ∘ Comma-homset.eq)

open comma-category public

_↓_ : {ℓ₁ ℓ′₁ ℓ″₁ ℓ₂ ℓ′₂ ℓ″₂ ℓ₃ ℓ′₃ ℓ″₃ : Level} {A : Category {ℓ₁} {ℓ′₁} {ℓ″₁}} {B : Category {ℓ₂} {ℓ′₂} {ℓ″₂}} {C : Category {ℓ₃} {ℓ′₃} {ℓ″₃}} (F : Functor A C) (G : Functor B C) → Category
_↓_ = Comma
