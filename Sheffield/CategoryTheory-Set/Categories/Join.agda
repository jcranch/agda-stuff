module Sheffield.CategoryTheory-Set.Categories.Join where

open import Level
open import Data.Sum
open import Relation.Binary.PropositionalEquality as PropEq using (_≡_ ; refl)

open import Sheffield.CategoryTheory-Set.Categories
open import Sheffield.CategoryTheory-Set.Functors


data join-homset {ℓ₁ ℓ₂ ℓ′₁ ℓ′₂ : Level} {A : Set ℓ₁} {B : Set ℓ₂} (m : A → A → Set ℓ′₁) (n : B → B → Set ℓ′₂) : (A ⊎ B) → (A ⊎ B) → Set (ℓ₁ ⊔ ℓ₂ ⊔ ℓ′₁ ⊔ ℓ′₂) where
  j-inj₁ : (x y : A) (f : m x y) → join-homset m n (inj₁ x) (inj₁ y)
  j-inj₂ : (x y : B) (f : n x y) → join-homset m n (inj₂ x) (inj₂ y)
  j-inj₁₂ : (x : A) (y : B) → join-homset m n (inj₁ x) (inj₂ y)


infixl 6 _✫_
_✫_ : {ℓ₁ ℓ₂ ℓ′₁ ℓ′₂ : Level} (C₁ : Category {ℓ₁} {ℓ′₁}) (C₂ : Category {ℓ₂} {ℓ′₂}) → Category {ℓ₁ ⊔ ℓ₂} {ℓ₁ ⊔ ℓ₂ ⊔ ℓ′₁ ⊔ ℓ′₂}

makeCat obj₁ hom₁ id₁ compose₁ id-l₁ id-r₁ assoc₁ ✫ makeCat obj₂ hom₂ id₂ compose₂ id-l₂ id-r₂ assoc₂ = makeCat obj hom id compose id-l id-r assoc where
  obj = obj₁ ⊎ obj₂

  hom = join-homset hom₁ hom₂

  id : (a : obj) → hom a a
  id (inj₁ x) = j-inj₁ x x (id₁ x)
  id (inj₂ y) = j-inj₂ y y (id₂ y)

  compose : {x y z : obj} → hom y z → hom x y → hom x z
  compose (j-inj₁ x' y f) (j-inj₁ x .x' f') = j-inj₁ x y (compose₁ f f')
  compose (j-inj₂ x' y f) (j-inj₂ x .x' f') = j-inj₂ x y (compose₂ f f')
  compose (j-inj₂ x' y f) (j-inj₁₂ x .x') = j-inj₁₂ x y
  compose (j-inj₁₂ x' y) (j-inj₁ x .x' f) = j-inj₁₂ x y

  id-l : {x y : obj} (f : hom x y) → compose (id y) f ≡ f
  id-l (j-inj₁ x y f) = PropEq.cong (j-inj₁ x y) (id-l₁ f)
  id-l (j-inj₂ x y f) = PropEq.cong (j-inj₂ x y) (id-l₂ f)
  id-l (j-inj₁₂ x y) = PropEq.refl

  id-r : {x y : obj} (f : hom x y) → compose f (id x) ≡ f
  id-r (j-inj₁ x y f) = PropEq.cong (j-inj₁ x y) (id-r₁ f)
  id-r (j-inj₂ x y f) = PropEq.cong (j-inj₂ x y) (id-r₂ f)
  id-r (j-inj₁₂ x y) = PropEq.refl

  assoc : {w x y z : obj} (h : hom y z) (g : hom x y) (f : hom w x) → compose h (compose g f) ≡ compose (compose h g) f
  assoc (j-inj₁ y z h) (j-inj₁ x .y g) (j-inj₁ w .x f) = PropEq.cong (j-inj₁ w z) (assoc₁ h g f)
  assoc (j-inj₂ y z h) (j-inj₂ x .y g) (j-inj₂ w .x f) = PropEq.cong (j-inj₂ w z) (assoc₂ h g f) 
  assoc (j-inj₂ y z h) (j-inj₂ x .y g) (j-inj₁₂ w .x) = PropEq.refl
  assoc (j-inj₂ y z h) (j-inj₁₂ x .y) (j-inj₁ w .x f) = PropEq.refl
  assoc (j-inj₁₂ y z) (j-inj₁ x .y g) (j-inj₁ w .x f) = PropEq.refl


in₁ : {ℓ₁ ℓ₂ ℓ′₁ ℓ′₂ : Level} {C₁ : Category {ℓ₁} {ℓ′₁}} {C₂ : Category {ℓ₂} {ℓ′₂}} → Functor C₁ (C₁ ✫ C₂)
in₁ = makeFunctor inj₁ (λ {x} {y} f → j-inj₁ x y f) (λ x → refl) (λ g f → refl)

in₂ : {ℓ₁ ℓ₂ ℓ′₁ ℓ′₂ : Level} {C₁ : Category {ℓ₁} {ℓ′₁}} {C₂ : Category {ℓ₂} {ℓ′₂}} → Functor C₂ (C₁ ✫ C₂)
in₂ = makeFunctor inj₂ (λ {x} {y} f → j-inj₂ x y f) (λ x → refl) (λ g f → refl)


infixl 6 _✫₁_
_✫₁_ : {ℓ₁ ℓ′₁ ℓ₂ ℓ′₂ ℓ₃ ℓ′₃ ℓ₄ ℓ′₄ : Level}
       {C₁ : Category {ℓ₁} {ℓ′₁}} {C₂ : Category {ℓ₂} {ℓ′₂}}
       {D₁ : Category {ℓ₃} {ℓ′₃}} {D₂ : Category {ℓ₄} {ℓ′₄}} →
       Functor C₁ D₁ → Functor C₂ D₂ → Functor (C₁ ✫ C₂) (D₁ ✫ D₂)
_✫₁_ {_} {_} {_} {_} {_} {_} {_} {_} {C₁} {C₂} {D₁} {D₂} (makeFunctor obj₁ hom₁ id₁ compose₁) (makeFunctor obj₂ hom₂ id₂ compose₂) = makeFunctor obj hom id compose where
  obj : Category.obj (C₁ ✫ C₂) → Category.obj (D₁ ✫ D₂)
  obj (inj₁ x) = inj₁ (obj₁ x)
  obj (inj₂ y) = inj₂ (obj₂ y)

  hom : {x y : Category.obj (C₁ ✫ C₂)} → Category.hom (C₁ ✫ C₂) x y → Category.hom (D₁ ✫ D₂) (obj x) (obj y)
  hom (j-inj₁ x y f) = j-inj₁ (obj₁ x) (obj₁ y) (hom₁ f)
  hom (j-inj₂ x y f) = j-inj₂ (obj₂ x) (obj₂ y) (hom₂ f)
  hom (j-inj₁₂ x y) = j-inj₁₂ (obj₁ x) (obj₂ y)

  id : (x : Category.obj (C₁ ✫ C₂)) → hom (Category.id (C₁ ✫ C₂) x) ≡ Category.id (D₁ ✫ D₂) (obj x)
  id (inj₁ x) = PropEq.cong (j-inj₁ (obj₁ x) (obj₁ x)) (id₁ x)
  id (inj₂ y) = PropEq.cong (j-inj₂ (obj₂ y) (obj₂ y)) (id₂ y)

  compose : {x y z : Category.obj (C₁ ✫ C₂)} (g : Category.hom (C₁ ✫ C₂) y z) (f : Category.hom (C₁ ✫ C₂) x y) → hom (Category.compose (C₁ ✫ C₂) g f) ≡ Category.compose (D₁ ✫ D₂) (hom g) (hom f)
  compose (j-inj₁ y z g) (j-inj₁ x .y f) = PropEq.cong (j-inj₁ (obj₁ x) (obj₁ z)) (compose₁ g f)
  compose (j-inj₁₂ y z) (j-inj₁ x .y f) = refl
  compose (j-inj₂ y z g) (j-inj₁₂ x .y) = refl
  compose (j-inj₂ y z g) (j-inj₂ x .y f) = PropEq.cong (j-inj₂ (obj₂ x) (obj₂ z)) (compose₂ g f)
