-- Categories consisting of two objects, and a set of morphisms between them.

module Sheffield.CategoryTheory-Setoid.Categories.Parallel where

open import Function.Equality hiding (id ; _⟶_) renaming (_⇨_ to _⟶_)
open import Level
open import Relation.Binary

open import Sheffield.CategoryTheory-Setoid.Categories
open import Sheffield.CategoryTheory-Setoid.Functors
open import Sheffield.CategoryTheory-Setoid.NaturalTransformations
open import Sheffield.CategoryTheory-Setoid.SetoidFunction


parallels : {ℓ ℓ′ : Level} → Setoid ℓ ℓ′ → Category

data parallel-obj : Set where
  source : parallel-obj
  target : parallel-obj

data parallel-homset {ℓ ℓ′ : Level} (A : Setoid ℓ ℓ′) : parallel-obj → parallel-obj → Set ℓ where
  id-s : parallel-homset A source source
  id-t : parallel-homset A target target
  parallel-map : Setoid.Carrier A → parallel-homset A source target

data parallel-≈ {ℓ ℓ′ : Level} (A : Setoid ℓ ℓ′) : (x y : parallel-obj) → Rel (parallel-homset A x y) (ℓ ⊔ ℓ′) where
  ≈-s : parallel-≈ A source source id-s id-s
  ≈-t : parallel-≈ A target target id-t id-t
  ≈-p : {x y : Setoid.Carrier A} → Setoid._≈_ A x y → parallel-≈ A source target (parallel-map x) (parallel-map y)


parallel-≈-refl : {ℓ ℓ′ : Level} (A : Setoid ℓ ℓ′) (x y : parallel-obj) (h : parallel-homset A x y) → parallel-≈ A x y h h
parallel-≈-refl A source source id-s = ≈-s
parallel-≈-refl A source target (parallel-map y) = ≈-p (Setoid.refl A)
parallel-≈-refl A target source ()
parallel-≈-refl A target target id-t = ≈-t

parallel-≈-sym : {ℓ ℓ′ : Level} (A : Setoid ℓ ℓ′) (x y : parallel-obj) (h h′ : parallel-homset A x y) → parallel-≈ A x y h h′ → parallel-≈ A x y h′ h
parallel-≈-sym A source source id-s id-s _ = ≈-s
parallel-≈-sym A source target (parallel-map y) (parallel-map y′) (≈-p e) = ≈-p (Setoid.sym A e)
parallel-≈-sym A target source () () e
parallel-≈-sym A target target id-t id-t _ = ≈-t

parallel-≈-trans : {ℓ ℓ′ : Level} (A : Setoid ℓ ℓ′) (x y : parallel-obj) (h h′ h″ : parallel-homset A x y) → parallel-≈ A x y h h′ → parallel-≈ A x y h′ h″ → parallel-≈ A x y h h″
parallel-≈-trans A source source id-s id-s id-s _ _ = ≈-s
parallel-≈-trans A source target (parallel-map y) (parallel-map y') (parallel-map y0) (≈-p e) (≈-p e′) = ≈-p (Setoid.trans A e e′)
parallel-≈-trans A target source () () () e e′
parallel-≈-trans A target target id-t id-t id-t e e′ = ≈-t


parallel-hom : {ℓ ℓ′ : Level} (A : Setoid ℓ ℓ′) (x y : parallel-obj) → Setoid ℓ (ℓ ⊔ ℓ′)
parallel-hom A x y = record {
  Carrier = parallel-homset A x y ;
  _≈_ = parallel-≈ A x y ;
  isEquivalence = record {
    refl = λ {h} → parallel-≈-refl A x y h ;
    sym = λ {i} {j} → parallel-≈-sym A x y i j ;
    trans = λ {i} {j} {k} → parallel-≈-trans A x y i j k } }


parallels A  = makeCat parallel-obj (parallel-hom A) id compose id-l id-r assoc where
  id : (x : parallel-obj) → parallel-homset A x x
  id source = id-s
  id target = id-t
  infix 7 _•_
  _•_ : {x y z : parallel-obj} (g : parallel-homset A y z) (f : parallel-homset A x y) → parallel-homset A x z
  g • id-s = g
  id-t • f = f
  •-cong : {x y z : parallel-obj} (g₁ g₂ : parallel-homset A y z) (f₁ f₂ : parallel-homset A x y) → parallel-≈ A y z g₁ g₂ → parallel-≈ A x y f₁ f₂ → parallel-≈ A x z (g₁ • f₁) (g₂ • f₂)
  •-cong id-s id-s id-s id-s _ _ = ≈-s
  •-cong (parallel-map g₁) (parallel-map g₂) id-s id-s g₁≈g₂ _ = g₁≈g₂
  •-cong id-t id-t (parallel-map f₁) (parallel-map f₂) _ f₁≈f₂ = f₁≈f₂
  •-cong id-t id-t id-t id-t _ _ = ≈-t

  compose : {x y z : parallel-obj} → Γ (parallel-hom A y z ⟶ parallel-hom A x y ⟶ parallel-hom A x z)
  compose = record {
    _⟨$⟩_ = λ g → record {
      _⟨$⟩_ = _•_ g ;
      cong = λ e → •-cong g g _ _ (parallel-≈-refl A _ _ g) e } ;
    cong = λ e₁ e₂ → •-cong _ _ _ _ e₁ e₂ }

  id-l : {x y : parallel-obj} (f : Γ (parallel-hom A x y)) → Setoid._≈_ (parallel-hom A x y) (compose ⟨$⟩ id y ⟨$⟩ f) f
  id-l id-s = ≈-s
  id-l id-t = ≈-t
  id-l (parallel-map y) = parallel-≈-refl A source target (parallel-map y)

  id-r : {x y : parallel-obj} (f : Γ (parallel-hom A x y)) → Setoid._≈_ (parallel-hom A x y) (compose ⟨$⟩ f ⟨$⟩ id x) f
  id-r id-s = ≈-s
  id-r id-t = ≈-t
  id-r (parallel-map y) = parallel-≈-refl A source target (parallel-map y)

  assoc : {w x y z : parallel-obj} (h : Γ (parallel-hom A y z)) (g : Γ (parallel-hom A x y)) (f : Γ (parallel-hom A w x)) → Setoid._≈_ (parallel-hom A w z) (compose ⟨$⟩ (compose ⟨$⟩ h ⟨$⟩ g) ⟨$⟩ f) (compose ⟨$⟩ h ⟨$⟩ (compose ⟨$⟩ g ⟨$⟩ f))
  assoc id-t id-t id-t = ≈-t
  assoc id-t id-t (parallel-map y) = parallel-≈-refl A source target (parallel-map y)
  assoc id-t (parallel-map y) id-s = parallel-≈-refl A source target (parallel-map y)
  assoc (parallel-map y) id-s id-s = parallel-≈-refl A source target (parallel-map y)
  assoc id-s id-s id-s = ≈-s



parallels-functor : {ℓ ℓ′ ℓ₁ ℓ′₁ ℓ″₁ : Level} {A : Setoid ℓ ℓ′}
  {C : Category {ℓ₁} {ℓ′₁} {ℓ″₁}} {s t : Category.obj C}
  (h : Γ (A ⟶ Category.hom C s t)) → Functor (parallels A) C
parallels-functor {A = A} {C = C} {s} {t} h = makeFunctor obj hom id compose where
  open Setoid A

  obj : parallel-obj → Category.obj C
  obj source = s
  obj target = t

  homsets : {x y : Category.obj (parallels A)} → Category.homset (parallels A) x y → Category.homset C (obj x) (obj y)
  homsets id-s = Category.id C s
  homsets id-t = Category.id C t
  homsets (parallel-map y) = h ⟨$⟩ y

  hom-cong : {x y : Category.obj (parallels A)} (f₁ f₂ : Category.homset (parallels A) x y) → parallel-≈ A x y f₁ f₂ → Setoid._≈_ (Category.hom C (obj x) (obj y)) (homsets f₁) (homsets f₂)
  hom-cong id-s id-s f₁≈f₂ = Setoid.refl (Category.hom C s s)
  hom-cong id-t id-t f₁≈f₂ = Setoid.refl (Category.hom C t t)
  hom-cong (parallel-map y) (parallel-map y') (≈-p e) = Π.cong h e

  hom : {x y : Category.obj (parallels A)} → Γ (Category.hom (parallels A) x y ⟶ Category.hom C (obj x) (obj y))
  hom = record {
    _⟨$⟩_ = homsets ;
    cong = λ x → hom-cong _ _ x }

  id : (x : Category.obj (parallels A)) → Setoid._≈_ (Category.hom C _ _) (hom ⟨$⟩ Category.id (parallels A) x) (Category.id C (obj x))
  id source = Setoid.refl (Category.hom C s s)
  id target = Setoid.refl (Category.hom C t t)

  compose : {x y z : Category.obj (parallels A)} (g : Γ (Category.hom (parallels A) y z)) (f : Γ (Category.hom (parallels A) x y)) → Setoid._≈_ (Category.hom C _ _) (hom ⟨$⟩ (Category._•_ (parallels A) g f)) (Category._•_ C (hom ⟨$⟩ g) (hom ⟨$⟩ f))
  compose id-t id-t = IsEquivalence.sym (Setoid.isEquivalence (Category.hom C _ _)) (Category.id-l C _)
  compose id-t (parallel-map y) = IsEquivalence.sym (Setoid.isEquivalence (Category.hom C _ _)) (Category.id-l C _)
  compose (parallel-map y) id-s = IsEquivalence.sym (Setoid.isEquivalence (Category.hom C _ _)) (Category.id-r C _)
  compose id-s id-s = IsEquivalence.sym (Setoid.isEquivalence (Category.hom C _ _)) (Category.id-l C _)


parallels-nat-trans : {ℓ ℓ′ ℓ₁ ℓ′₁ ℓ″₁ : Level} {A : Setoid ℓ ℓ′} {C : Category {ℓ₁} {ℓ′₁} {ℓ″₁}}
  (F G : Functor (parallels A) C)
  (source₁ : Category.homset C (Functor.obj F source) (Functor.obj G source))
  (target₁ : Category.homset C (Functor.obj F target) (Functor.obj G target))
  (n : (a : Setoid.Carrier A) → Setoid._≈_ (Category.hom C _ _) (Category._•_ C target₁ (Functor.homsets F (parallel-map a))) (Category._•_ C (Functor.homsets G (parallel-map a)) source₁)) → NatTrans F G
parallels-nat-trans {A = A} {C = C} F G s₁ t₁ n = makeNatTrans component naturality where
  component : (x : Category.obj (parallels A)) → Category.homset C (Functor.obj F x) (Functor.obj G x)
  component source = s₁
  component target = t₁
  naturality : {x y : Category.obj (parallels A)} (f : Category.homset (parallels A) x y) → Setoid._≈_ (Category.hom C _ _) (Category._•_ C (component y) (Functor.homsets F f)) (Category._•_ C (Functor.homsets G f) (component x))
  naturality id-s = naturality-for-identities F G source s₁
  naturality id-t = naturality-for-identities F G target t₁
  naturality (parallel-map y) = n y


