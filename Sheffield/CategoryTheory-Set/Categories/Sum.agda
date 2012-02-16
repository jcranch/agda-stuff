module Sheffield.CategoryTheory-Set.Categories.Sum where

open import Data.Sum renaming (_⊎_ to _+_)
open import Level
open import Relation.Binary.PropositionalEquality as PropEq using (_≡_ ; refl)

open import Sheffield.CategoryTheory-Set.Categories
open import Sheffield.CategoryTheory-Set.Functors
open import Sheffield.CategoryTheory-Set.NaturalTransformations



data sum-hom  {ℓ₁ ℓ₂ ℓ′₁ ℓ′₂ : Level} {A : Set ℓ₁} {B : Set ℓ₂} (m : A → A → Set ℓ′₁) (n : B → B → Set ℓ′₂) : (A + B) → (A + B) → Set (ℓ₁ ⊔ ℓ₂ ⊔ ℓ′₁ ⊔ ℓ′₂) where
  ssi₁ : (x : A) (y : A) (f : m x y) → sum-hom m n (inj₁ x) (inj₁ y)
  ssi₂ : (x : B) (y : B) (f : n x y) → sum-hom m n (inj₂ x) (inj₂ y)

infixl 5 _⊎_
_⊎_ :  {ℓ₁ ℓ₂ ℓ′₁ ℓ′₂ : Level} (C₁ : Category {ℓ₁} {ℓ′₁}) (C₂ : Category {ℓ₂} {ℓ′₂}) → Category {ℓ₁ ⊔ ℓ₂} {ℓ₁ ⊔ ℓ₂ ⊔ ℓ′₁ ⊔ ℓ′₂}
makeCat obj₁ hom₁ id₁ compose₁ id-l₁ id-r₁ assoc₁ ⊎ makeCat obj₂ hom₂ id₂ compose₂ id-l₂ id-r₂ assoc₂ = makeCat obj hom id compose id-l id-r assoc where
  obj = obj₁ + obj₂
  hom = sum-hom hom₁ hom₂
  id : (x : obj) → hom x x
  id (inj₁ x) = ssi₁ x x (id₁ x)
  id (inj₂ y) = ssi₂ y y (id₂ y)
  compose : {x y z : obj} → hom y z → hom x y → hom x z
  compose (ssi₁ y z g) (ssi₁ x .y f) = ssi₁ x z (compose₁ g f)
  compose (ssi₂ y z g) (ssi₂ x .y f) = ssi₂ x z (compose₂ g f)
  id-l : {x y : obj} (f : hom x y) → compose (id y) f ≡ f
  id-l (ssi₁ x y f) = PropEq.cong (ssi₁ x y) (id-l₁ f)
  id-l (ssi₂ x y f) = PropEq.cong (ssi₂ x y) (id-l₂ f)
  id-r : {x y : obj} (f : hom x y) → compose f (id x) ≡ f
  id-r (ssi₁ x y f) = PropEq.cong (ssi₁ x y) (id-r₁ f)
  id-r (ssi₂ x y f) = PropEq.cong (ssi₂ x y) (id-r₂ f)
  assoc : {w x y z : obj} (h : hom y z) (g : hom x y) (f : hom w x) → compose h (compose g f) ≡ compose (compose h g) f
  assoc (ssi₁ y z h) (ssi₁ x .y g) (ssi₁ w .x f) = PropEq.cong (ssi₁ w z) (assoc₁ h g f)
  assoc (ssi₂ y z h) (ssi₂ x .y g) (ssi₂ w .x f) = PropEq.cong (ssi₂ w z) (assoc₂ h g f)


⊎-functor : {ℓ₁ ℓ₂ ℓ ℓ′₁ ℓ′₂ ℓ′ : Level} {C₁ : Category {ℓ₁} {ℓ′₁}} {C₂ : Category {ℓ₂} {ℓ′₂}} {D : Category {ℓ} {ℓ′}} → Functor C₁ D → Functor C₂ D → Functor (C₁ ⊎ C₂) D
⊎-functor {_} {_} {_} {_} {_} {_} {C₁} {C₂} {D} (makeFunctor obj₁ hom₁ id₁ compose₁) (makeFunctor obj₂ hom₂ id₂ compose₂) = makeFunctor obj hom id assoc where
  obj = [ obj₁ , obj₂ ]′

  hom : {x y : Category.obj (C₁ ⊎ C₂)} → Category.hom (C₁ ⊎ C₂) x y → Category.hom D (obj x) (obj y)
  hom {inj₁ x} {inj₁ y} (ssi₁ .x .y f) = hom₁ f
  hom {inj₁ x} {inj₂ y} ()
  hom {inj₂ x} {inj₁ y} ()
  hom {inj₂ x} {inj₂ y} (ssi₂ .x .y f) = hom₂ f

  id : (x : Category.obj (C₁ ⊎ C₂)) → hom (Category.id (C₁ ⊎ C₂) x) ≡ Category.id D (obj x)
  id (inj₁ x) = id₁ x
  id (inj₂ y) = id₂ y

  assoc : {x y z : Category.obj (C₁ ⊎ C₂)} (g : Category.hom (C₁ ⊎ C₂) y z) (f : Category.hom (C₁ ⊎ C₂) x y) → hom (Category.compose (C₁ ⊎ C₂) g f) ≡ Category.compose D (hom g) (hom f)
  assoc {inj₁ x} {inj₁ y} {inj₁ z} (ssi₁ .y .z g) (ssi₁ .x .y f) = compose₁ g f
  assoc {inj₁ x} {inj₁ y} {inj₂ z} () (ssi₁ .x .y f)
  assoc {inj₁ x} {inj₂ y} {inj₁ z} () ()
  assoc {inj₁ x} {inj₂ y} {inj₂ z} (ssi₂ .y .z g) ()
  assoc {inj₂ x} {inj₁ y} {inj₁ z} (ssi₁ .y .z g) ()
  assoc {inj₂ x} {inj₁ y} {inj₂ z} () ()
  assoc {inj₂ x} {inj₂ y} {inj₁ z} () (ssi₂ .x .y f)
  assoc {inj₂ x} {inj₂ y} {inj₂ z} (ssi₂ .y .z g) (ssi₂ .x .y f) = compose₂ g f


in₁ :  {ℓ₁ ℓ₂ ℓ′₁ ℓ′₂ : Level} {C₁ : Category {ℓ₁} {ℓ′₁}} {C₂ : Category {ℓ₂} {ℓ′₂}} → Functor C₁ (C₁ ⊎ C₂)
in₁ = makeFunctor inj₁ (λ {x} {y} f → ssi₁ x y f) (λ x → refl) (λ g f → refl)

in₂ :  {ℓ₁ ℓ₂ ℓ′₁ ℓ′₂ : Level} {C₁ : Category {ℓ₁} {ℓ′₁}} {C₂ : Category {ℓ₂} {ℓ′₂}} → Functor C₂ (C₁ ⊎ C₂)
in₂ = makeFunctor inj₂ (λ {x} {y} f → ssi₂ x y f) (λ x → refl) (λ g f → refl)
