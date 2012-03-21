-- The theory of categories; this is a full-featured version where we have
-- a set of objects and, for any two, a setoid of morphisms between them.

module Sheffield.CategoryTheory-Setoid.Categories where


open import Algebra.Structures
open import Function using (flip)
open import Function.Equality hiding (id ; _⟶_) renaming (_⇨_ to _⟶_)
open import Level
open import Relation.Binary
import Relation.Binary.EqReasoning as EqR


open import Sheffield.CategoryTheory-Setoid.SetoidFunction renaming (flip to flip′)



record Category {ℓ ℓ′ ℓ″ : Level} : Set (suc (ℓ ⊔ ℓ′ ⊔ ℓ″)) where
  constructor makeCat

  field
    obj : Set ℓ
    hom : obj  → obj → Setoid ℓ′ ℓ″
    id : (x : obj) → Γ (hom x x)
    compose : {x y z : obj} → Γ (hom y z ⟶ hom x y ⟶ hom x z)

  homset : obj → obj → Set ℓ′
  homset x y = Γ (hom x y)

  infixr 7 _•_
  _•_ : {x y z : obj} → homset y z → homset x y → homset x z
  _•_ = λ g f → compose ⟨$⟩ g ⟨$⟩ f

  infix 4 _≈_
  _≈_ : {x y : obj} → Rel (homset x y) ℓ″
  _≈_ {x} {y} = Setoid._≈_ (hom x y)

  ≈-refl : {x y : obj} {f : homset x y} → f ≈ f
  ≈-refl {x} {y} {f} = Setoid.refl (hom x y)

  ≈-sym : {x y : obj} {f g : homset x y} → f ≈ g → g ≈ f
  ≈-sym {x} {y} f≈g = Setoid.sym (hom x y) f≈g

  ≈-trans : {x y : obj} {f g h : homset x y} → f ≈ g → g ≈ h → f ≈ h
  ≈-trans {x} {y} f≈g g≈h = Setoid.trans (hom x y) f≈g g≈h

  •-cong : {x y z : obj} {g₁ g₂ : homset y z} {f₁ f₂ : homset x y} → g₁ ≈ g₂ → f₁ ≈ f₂ → (g₁ • f₁) ≈ (g₂ • f₂)
  •-cong g₁≈g₂ f₁≈f₂ = cong compose g₁≈g₂ f₁≈f₂

  field
    id-l : {x y : obj} (f : homset x y) → (id y • f) ≈ f
    id-r : {x y : obj} (f : homset x y) → (f • id x) ≈ f
    assoc : {w x y z : obj} (h : homset y z) (g : homset x y) (f : homset w x) → ((h • g) • f) ≈ (h • (g • f))

  module ≈-Reasoning (x : obj) (y : obj) = EqR (hom x y)



module endomorphisms {ℓ ℓ′ ℓ″ : Level} {C : Category {ℓ} {ℓ′} {ℓ″}} where

  open import Data.Product
  open Category C

  endomorphismMonoid : (x : obj) → IsMonoid (_≈_ {x} {x}) _•_ (id x)

  endomorphismMonoid x = record {
    isSemigroup = record { 
      isEquivalence = Setoid.isEquivalence (hom x x) ;
      assoc = assoc ;
      ∙-cong = •-cong } ;
    identity = id-l ,′ id-r }

open endomorphisms public



opposite : {ℓ ℓ′ ℓ″ : Level} → Category {ℓ} {ℓ′} {ℓ″} → Category {ℓ} {ℓ′} {ℓ″}
opposite (makeCat obj hom id compose id-l id-r assoc) = makeCat obj (flip hom) id (flip′ ⟨$⟩ compose) id-r id-l (λ {w} {x} {y} {z} h g f → Setoid.sym (hom z w) (assoc f g h))



module Iso {ℓ ℓ′ ℓ″ : Level} (C : Category {ℓ} {ℓ′} {ℓ″}) where

  open Category C

  record Isomorphism {x y : obj} (obverse : homset x y) : Set (ℓ′ ⊔ ℓ″) where
    constructor makeIso
    field
      reverse : homset y x
      unit : reverse • obverse ≈ id x
      counit : obverse • reverse ≈ id y

  record _≅_ (x y : obj) : Set (ℓ′ ⊔ ℓ″) where
    constructor make-≅
    field
      obverse : homset x y
      iso : Isomorphism obverse
    open Isomorphism iso public

  make-iso : {x y : obj} (f : homset x y) (f⁻¹ : homset y x) (unit : f⁻¹ • f ≈ id x) (counit : f • f⁻¹ ≈ id y) → x ≅ y
  make-iso f f⁻¹ unit counit = make-≅ f (makeIso f⁻¹ unit counit)

  left-right-inverses-agree : {x y : obj} {f : Γ (hom x y)} {fl fr : Γ (hom y x)} → fl • f ≈ id x → f • fr ≈ id y → fl ≈ fr
  left-right-inverses-agree {x} {y} {f} {fl} {fr} fli fri = begin
    fl
      ≈⟨ ≈-sym (id-r fl) ⟩
    fl • (id y)
      ≈⟨ •-cong ≈-refl (≈-sym fri) ⟩
    fl • (f • fr)
      ≈⟨ ≈-sym (assoc fl f fr) ⟩
    (fl • f) • fr
      ≈⟨ •-cong fli ≈-refl ⟩
    (id x) • fr
      ≈⟨ id-l fr ⟩
    fr ∎ where open ≈-Reasoning y x

  double-cancellation : {x y z : obj}
                        {f : homset x y} {f⁻¹ : homset y x}
                        {g : homset y z} {g⁻¹ : homset z y} →
                        f⁻¹ • f ≈ id x →
                        g⁻¹ • g ≈ id y →
                        (f⁻¹ • g⁻¹) • (g • f) ≈ id x
  double-cancellation {x} {y} {z} {f} {f⁻¹} {g} {g⁻¹} ef eg = begin
    (f⁻¹ • g⁻¹) • (g • f)
      ≈⟨ ≈-sym (assoc (f⁻¹ • g⁻¹) g f) ⟩
    ((f⁻¹ • g⁻¹) • g) • f
      ≈⟨ •-cong (assoc f⁻¹ g⁻¹ g) ≈-refl ⟩
    (f⁻¹ • (g⁻¹ • g)) • f
      ≈⟨ •-cong (•-cong ≈-refl eg) ≈-refl ⟩
    (f⁻¹ • (id y)) • f
      ≈⟨ •-cong (id-r f⁻¹) ≈-refl ⟩
    f⁻¹ • f
      ≈⟨ ef ⟩
    id x ∎ where open ≈-Reasoning x x

  inverse : {x y : obj} {f : homset x y} → Isomorphism f → homset y x
  inverse (makeIso f⁻¹ unit counit) = f⁻¹

  inverse-unique : {x y : obj} (f : homset x y) (i₁ i₂ : Isomorphism f) → inverse i₁ ≈ inverse i₂
  inverse-unique f (makeIso _ unit _) (makeIso _ _ counit') = left-right-inverses-agree unit counit'

  iso-refl : (x : obj) → Isomorphism (id x)
  iso-refl x = makeIso (id x) (id-l (id x)) (id-r (id x))

  iso-sym : {x y : obj} {f : homset x y} (i : Isomorphism f) → Isomorphism (inverse i)
  iso-sym {x} {y} {f} (makeIso f⁻¹ unit counit) = makeIso f counit unit

  iso-trans : {x y z : obj} {g : homset y z} {f : homset x y} → Isomorphism g → Isomorphism f → Isomorphism (g • f)
  iso-trans {x} {y} {z} {g} {f} (makeIso g⁻¹ unit-g counit-g) (makeIso f⁻¹ unit-f counit-f) = makeIso (f⁻¹ • g⁻¹) (double-cancellation unit-f unit-g) (double-cancellation counit-g counit-f)

  ≅-refl : {x : obj} → x ≅ x
  ≅-refl {x} = make-≅ (id x) (iso-refl x)

  ≅-sym : {x y : obj} → x ≅ y → y ≅ x
  ≅-sym (make-≅ f i) = make-≅ (inverse i) (iso-sym i)

  ≅-trans : {x y z : obj} → x ≅ y → y ≅ z → x ≅ z
  ≅-trans (make-≅ f i) (make-≅ g j) = make-≅ (g • f) (iso-trans j i)

  classes : Setoid ℓ (ℓ′ ⊔ ℓ″)
  classes = record {
    Carrier = obj;
    _≈_ = _≅_;
    isEquivalence = record {
      refl = ≅-refl;
      sym = ≅-sym;
      trans = ≅-trans } }

open Iso




module OppositeIso where

  opposite-iso : {ℓ ℓ′ ℓ″ : Level} {C : Category {ℓ} {ℓ′} {ℓ″}} {x y : Category.obj C} {f : Category.homset C x y} → Isomorphism C f → Isomorphism (opposite C) f
  opposite-iso {ℓ} {ℓ′} {C} {x} {y} {f} (makeIso f⁻¹ unit counit) = makeIso f⁻¹ counit unit




-- since epimorphisms are defined as monomorphisms in the opposite category,
-- these facts about monomorphisms will work for epimorphisms just the same.
module monomorphisms {ℓ ℓ′ ℓ″ : Level} (C : Category {ℓ} {ℓ′} {ℓ″}) where

  open Category C

  monomorphism : {x y : obj} (f : homset x y) → Set (ℓ ⊔ ℓ′ ⊔ ℓ″)
  monomorphism {x} {y} f = {w : obj} (g₁ g₂ : homset w x) → f • g₁ ≈ f • g₂ → g₁ ≈ g₂

  monomorphism-compose : {x y z : obj} (g : homset y z) (f : homset x y) → monomorphism g → monomorphism f → monomorphism (g • f)
  monomorphism-compose g f g-mono f-mono h₁ h₂ e = f-mono h₁ h₂ (g-mono (f • h₁) (f • h₂) (≈-trans (≈-sym (assoc _ _ _)) (≈-trans e (assoc _ _ _))))

  monomorphism-cancel : {x y z : obj} (g : homset y z) (f : homset x y) → monomorphism (g • f) → monomorphism f
  monomorphism-cancel g f gf-mono h₁ h₂ e = gf-mono h₁ h₂ (≈-trans (assoc _ _ _) (≈-trans (•-cong ≈-refl e) (≈-sym (assoc _ _ _))))

  isomorphism-monomorphism : {x y : obj} {f : homset x y} (f-iso : Isomorphism C f) → monomorphism f
  isomorphism-monomorphism {x} {y} {f} (makeIso f⁻¹ unit counit) {w} g₁ g₂ e = begin
    g₁
      ≈⟨ ≈-sym (id-l g₁) ⟩
    (id x) • g₁
      ≈⟨ •-cong (≈-sym unit) ≈-refl ⟩
    (f⁻¹ • f) • g₁
      ≈⟨ assoc _ _ _ ⟩
    f⁻¹ • (f • g₁)
      ≈⟨ •-cong ≈-refl e ⟩
    f⁻¹ • (f • g₂)
      ≈⟨ ≈-sym (assoc _ _ _) ⟩
    (f⁻¹ • f) • g₂
      ≈⟨ •-cong unit ≈-refl ⟩
    (id x) • g₂
      ≈⟨ id-l g₂ ⟩
    g₂ ∎ where open ≈-Reasoning w x

open monomorphisms public

epimorphism : {ℓ ℓ′ ℓ″ : Level} (C : Category {ℓ} {ℓ′} {ℓ″}) {x y : Category.obj C} (f : Category.homset C x y) → Set (ℓ ⊔ ℓ′ ⊔ ℓ″)
epimorphism C f = monomorphism (opposite C) f



full-subcategory : {ℓ ℓ′ ℓ″ ℓ⁺ : Level} (C : Category {ℓ} {ℓ′} {ℓ″}) {O : Set ℓ⁺} (f : O → Category.obj C) → Category {ℓ⁺} {ℓ′} {ℓ″}
full-subcategory C {O} f = record {
  obj = O ;
  hom = λ x y → hom (f x) (f y) ;
  compose = λ {x} {y} {z} → compose {f x} {f y} {f z} ;
  id = λ x → id (f x) ;
  id-l = λ {x} {y} → id-l ;
  id-r = λ {x} {y} → id-r ;
  assoc = λ {w} {x} {y} {z} → assoc } where
  open Category C



module liftings-for-categories {ℓ ℓ′ ℓ″ ℓ₁ ℓ′₁ ℓ″₁ : Level} (C : Category {ℓ} {ℓ′} {ℓ″}) where

  open Category C

  category-lift : Category {ℓ ⊔ ℓ₁} {ℓ′ ⊔ ℓ′₁} {ℓ″ ⊔ ℓ″₁}
  category-lift = record {
    obj = Lift {ℓ} {ℓ₁} obj ;
    hom = λ x y → setoid-lift {ℓ′} {ℓ′₁} {ℓ″} {ℓ″₁} (hom (lower x) (lower y)) ;
    id = λ x → lift (id (lower x)) ;
    compose = λ {x} {y} {z} → record {
      _⟨$⟩_ = λ g → record {
        _⟨$⟩_ = λ f → lift (compose ⟨$⟩ lower g ⟨$⟩ lower f);
        cong = λ {f₁} {f₂} ε → lift (•-cong ≈-refl (lower ε)) };
      cong = λ {g₁} {g₂} e {f₁} {f₂} ε → lift (•-cong (lower e) (lower ε)) } ;
    id-l = λ {x} {y} f → lift (id-l _) ;
    id-r = λ {x} {y} f → lift (id-r _) ;
    assoc = λ {w} {x} {y} {z} h g f → lift (assoc _ _ _) }

open liftings-for-categories public