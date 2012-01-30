module Limits where

open import Data.Sum using (inj₁ ; inj₂)
open import Data.Unit
open import Level
open import Relation.Binary.PropositionalEquality

open import Categories
open import Categories.Diagrams using (point)
open import Categories.Join
open import Functors
open import Functors.Equality
open import NaturalTransformations



-- to do
--   definitions of limits
--   explicit induced maps of cones
--   application to zero maps




-- Cones can be thought of either as functors from a join category, or as natural tranformations from a constant functor

module cone-definitions-agree {ℓ₁ ℓ₂ ℓ′₁ ℓ′₂ : Level} (K : Category {ℓ₁} {ℓ′₁}) (C : Category {ℓ₂} {ℓ′₂}) where

  conesˡ : (F : Functor (point ✫ K) C) → NatTrans (constFunctor K C (Functor.obj F (inj₁ tt))) (F ⊙ in₂)
  conesˡ F = makeNatTrans component naturality where
    open ≡-Reasoning
    open Category C
    open Category (point ✫ K) hiding (id ; id-r) renaming (_•_ to _•′_) 

    F₀ = Functor.obj F
    F₁ = λ {x} {y} f → Functor.hom F {x} {y} f

    component : (x : Category.obj K) → Category.hom C (Functor.obj (constFunctor K C (Functor.obj F (inj₁ tt))) x) (Functor.obj (F ⊙ in₂) x)
    component x = Functor.hom F (j-inj₁₂ tt x)

    naturality : {x y : Category.obj K} (f : Category.hom K x y) → Category.compose C (component y) (Functor.hom (constFunctor K C (Functor.obj F (inj₁ tt))) f) ≡ Category.compose C (Functor.hom (F ⊙ in₂) f) (component x)
    naturality {x} {y} f = begin
      F₁ (j-inj₁₂ tt y) • id (F₀ (inj₁ tt))
        ≡⟨ id-r (F₁ (j-inj₁₂ tt y)) ⟩
      F₁ (j-inj₁₂ tt y)
        ≡⟨ refl ⟩
      Functor.hom F (j-inj₂ x y f •′ j-inj₁₂ tt x)
        ≡⟨ Functor.compose F (j-inj₂ x y f) (j-inj₁₂ tt x) ⟩
      Functor.hom F (j-inj₂ x y f) • Functor.hom F (j-inj₁₂ tt x) ∎

  conesʳ : (a : Category.obj C) (F : Functor K C) → NatTrans (constFunctor K C a) F → Functor (point ✫ K) C
  conesʳ a F (makeNatTrans Θ₀ Θ₁) = makeFunctor obj hom id assoc where
    F₀ = Functor.obj F

    obj : Category.obj (point ✫ K) → Category.obj C
    obj (inj₁ tt) = a
    obj (inj₂ y) = F₀ y

    hom : {x y : Category.obj (point ✫ K)} → Category.hom (point ✫ K) x y → Category.hom C (obj x) (obj y)
    hom (j-inj₁ x y f) = Category.id C a
    hom (j-inj₂ x y f) = Functor.hom F f
    hom (j-inj₁₂ x y) = Θ₀ y

    id : (x : Category.obj (point ✫ K)) → hom (Category.id (point ✫ K) x) ≡ Category.id C (obj x)
    id (inj₁ x) = refl
    id (inj₂ y) = Functor.id F y

    assoc : {x y z : Category.obj (point ✫ K)} (g : Category.hom (point ✫ K) y z) (f : Category.hom (point ✫ K) x y) → hom (Category.compose (point ✫ K) g f) ≡ Category.compose C (hom g) (hom f)
    assoc (j-inj₁ y z g) (j-inj₁ x .y f) = sym (Category.id-l C (Category.id C a))
    assoc (j-inj₂ y z g) (j-inj₂ x .y f) = Functor.compose F g f
    assoc (j-inj₂ y z g) (j-inj₁₂ x .y) = trans (sym (Category.id-r C (Θ₀ z))) (Θ₁ g)
    assoc (j-inj₁₂ y z) (j-inj₁ x .y f) = sym (Category.id-r C (Θ₀ z))

open cone-definitions-agree public

{-

module limits {ℓ₁ ℓ₂ ℓ′₁ ℓ′₂ : Level}
  {K : Category {ℓ₁} {ℓ′₁}} {C : Category {ℓ₂} {ℓ′₂}}
  (F : Functor K C) (x : Category.obj C) where

  IsLimit  (on a cone defined each of two ways)

  IsLimit = IsRightKanExtension (constFunctor K point tt) F (constFunctor point C x) ((and something representing the cone structure))

open limits public

-}