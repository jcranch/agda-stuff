module AbelianCategories.Zero where

open import Level
open import Relation.Binary.PropositionalEquality

open import Categories
open import Limits
open import Limits.Terminal
open import Misc


record IsZero-obj {ℓ₁ ℓ′₁ : Level} (C : Category {ℓ₁} {ℓ′₁}) (z : Category.obj C) : Set (ℓ₁ ⊔ ℓ′₁) where
  constructor make-zero-obj
  field
    term : IsTerminal C z
    init : IsInitial C z
  exists-to-0 = exists-to-1 C z term
  exists-from-0 = exists-to-1 (opposite C) z init
  unique-to-0 = λ {x} → unique-to-1 C z term {x}
  unique-from-0 = λ {x} → unique-to-1 (opposite C) z init {x}


zero-obj-opposite : {ℓ₁ ℓ′₁ : Level} (C : Category {ℓ₁} {ℓ′₁}) (z : Category.obj C) (z₀ : IsZero-obj C z) → IsZero-obj (opposite C) z
zero-obj-opposite C z (make-zero-obj term init) = make-zero-obj init term′ where
  term′ = (terminal↑ z (lowbrow-1 (exists-to-1 C z term) (unique-to-1 C z term)))


module zeroes {ℓ₁ ℓ′₁ : Level} (C : Category {ℓ₁} {ℓ′₁}) {z : Category.obj C} (z₀ : IsZero-obj C z) where

  open Category C

  open IsZero-obj z₀

  -- we make the zero object part of the type to ensure that the structure of being a zero morphism is unique
  data IsZero-hom {x y : obj} : hom x y → Set ℓ′₁ where
    make-zero-hom : (g : hom z y) (f : hom x z) → IsZero-hom (g • f)


  initial-morphism-zero : {x : obj} (f : hom z x) → IsZero-hom f
  initial-morphism-zero f = subst IsZero-hom (id-r f) (make-zero-hom f (id z))

  terminal-morphism-zero : {x : obj} (f : hom x z) → IsZero-hom f
  terminal-morphism-zero f = subst IsZero-hom (id-l f) (make-zero-hom (id z) f)



  zero-hom-witness : (x y : obj) → hom x y
  zero-hom-witness x y = exists-to-1 (opposite C) z init y • exists-to-1 C z term x

  zero-hom-satisfies : (x y : obj) → IsZero-hom (zero-hom-witness x y)
  zero-hom-satisfies x y = make-zero-hom (exists-to-1 (opposite C) z init y) (exists-to-1 C z term x)

  zero-hom-unique : {x y : obj} (f : hom x y) → IsZero-hom f → f ≡ zero-hom-witness x y
  zero-hom-unique {x} {y} .(g • f) (make-zero-hom g f) = cong₂ (Category.compose C) (unique-to-1 (opposite C) z init g) (unique-to-1 C z term f)

  zero-hom-existsUnique : (x y : obj) → existsUnique (hom x y) _≡_ IsZero-hom
  zero-hom-existsUnique x y = makeUnique (zero-hom-witness x y) (zero-hom-satisfies x y) zero-hom-unique

  zeroes-equal : {x y : obj} (f g : hom x y) → IsZero-hom f → IsZero-hom g → f ≡ g
  zeroes-equal {x} {y} f g f₀ g₀ = anyTwoSimilar isEquivalence (zero-hom-existsUnique x y) f₀ g₀



  zero-compose-l : {a b c : obj} (g : hom b c) (f : hom a b) (g₀ : IsZero-hom g) → IsZero-hom (g • f)
  zero-compose-l .(g′ • g) f (make-zero-hom g′ g) = subst IsZero-hom (assoc g′ g f) (make-zero-hom g′ (g • f))

  zero-compose-r : {a b c : obj} (g : hom b c) (f : hom a b) (f₀ : IsZero-hom f) → IsZero-hom (g • f)
  zero-compose-r  g .(f′ • f) (make-zero-hom f′ f) = subst IsZero-hom (sym (assoc g f′ f)) (make-zero-hom (g • f′) f)

  zero-compose-mono : {a b c : obj} (g : hom b c) (f : hom a b) → monomorphism C g → IsZero-hom (g • f) → IsZero-hom f
  zero-compose-mono {a} {b} {c} g f g-mono gf₀ = subst IsZero-hom (g-mono (zero-hom-witness a b) f (anyTwoSimilar isEquivalence (zero-hom-existsUnique a c) (zero-compose-r g (zero-hom-witness a b) (zero-hom-satisfies a b)) gf₀)) (zero-hom-satisfies a b)


open zeroes public
