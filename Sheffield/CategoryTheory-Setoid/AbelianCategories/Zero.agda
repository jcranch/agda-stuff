module Sheffield.CategoryTheory-Setoid.AbelianCategories.Zero where

open import Level
open import Relation.Binary

open import Sheffield.CategoryTheory-Setoid.Categories
open import Sheffield.CategoryTheory-Setoid.Categories.Equivalence
open import Sheffield.CategoryTheory-Setoid.Categories.Properties
open import Sheffield.CategoryTheory-Setoid.Terminal
open import Sheffield.CategoryTheory-Setoid.Terminal.Properties


record IsZero-obj {ℓ₁ ℓ′₁ ℓ″₁ : Level} (C : Category {ℓ₁} {ℓ′₁} {ℓ″₁}) (z : Category.obj C) : Set (ℓ₁ ⊔ ℓ′₁ ⊔ ℓ″₁) where
  constructor make-zero-obj
  field
    term : IsTerminal C z
    init : IsInitial C z
  exists-to-0 = IsTerminal.exists C term
  exists-from-0 = IsTerminal.exists (opposite C) init
  unique-to-0 = λ {x} → IsTerminal.unique C term {x}
  unique-from-0 = λ {x} → IsTerminal.unique (opposite C) init {x}


zero-obj-opposite : {ℓ₁ ℓ′₁ ℓ″₁ : Level} (C : Category {ℓ₁} {ℓ′₁} {ℓ″₁}) {z : Category.obj C} (z₀ : IsZero-obj C z) → IsZero-obj (opposite C) z
zero-obj-opposite C {z} (make-zero-obj term init) = make-zero-obj init term′ where
  term′ = terminal-preservation (introduce-opop C) (_≅₀_.reverse-isEquivalence₀ (opop-equivalence C)) z term


module zeroes {ℓ₁ ℓ′₁ ℓ″₁ : Level} (C : Category {ℓ₁} {ℓ′₁} {ℓ″₁}) {z : Category.obj C} (z₀ : IsZero-obj C z) where

  open Category C
  open IsZero-obj z₀

  data IsZero-hom {x y : obj} (h : homset x y) : Set (ℓ′₁ ⊔ ℓ″₁) where
    make-zero-hom : (g : homset z y) (f : homset x z) → g • f ≈ h → IsZero-hom h

  zeroes-stable : {x y : obj} (f g : homset x y) → IsZero-hom f → f ≈ g → IsZero-hom g
  zeroes-stable f g (make-zero-hom f₂ f₁ e) f≈g = make-zero-hom f₂ f₁ (≈-trans e f≈g)

  initial-morphism-zero : {x : obj} (f : homset z x) → IsZero-hom f
  initial-morphism-zero f = make-zero-hom f (id z) (id-r _)

  terminal-morphism-zero : {x : obj} (f : homset x z) → IsZero-hom f
  terminal-morphism-zero f = make-zero-hom (id z) f (id-l _)

  zero-hom-witness : (x y : obj) → homset x y
  zero-hom-witness x y = exists-from-0 y • exists-to-0 x

  zero-hom-satisfies : (x y : obj) → IsZero-hom (zero-hom-witness x y)
  zero-hom-satisfies x y = make-zero-hom (exists-from-0 y) (exists-to-0 x) ≈-refl

  zero-hom-unique : {x y : obj} (f : homset x y) → IsZero-hom f → f ≈ zero-hom-witness x y
  zero-hom-unique h (make-zero-hom g f e) = ≈-trans (≈-sym e) (•-cong (unique-from-0 g) (unique-to-0 f)) 

  zeroes-equal : {x y : obj} (f g : homset x y) → IsZero-hom f → IsZero-hom g → f ≈ g
  zeroes-equal f g f₀ g₀ = ≈-trans (zero-hom-unique f f₀) (≈-sym (zero-hom-unique g g₀))

  zero-compose-l : {a b c : obj} (g : homset b c) (f : homset a b) (g₀ : IsZero-hom g) → IsZero-hom (g • f)
  zero-compose-l hg f (make-zero-hom h g e) = make-zero-hom h (g • f) (≈-trans (≈-sym (assoc _ _ _)) (•-cong e ≈-refl))

  zero-compose-r : {a b c : obj} (g : homset b c) (f : homset a b) (f₀ : IsZero-hom f) → IsZero-hom (g • f)
  zero-compose-r h gf (make-zero-hom g f e) = make-zero-hom (h • g) f (≈-trans (assoc _ _ _) (•-cong ≈-refl e))

  zero-compose-mono : {a b c : obj} (g : homset b c) (f : homset a b) → monomorphism C g → IsZero-hom (g • f) → IsZero-hom f
  zero-compose-mono {a} {b} {c} g f g⁺ gf₀ = zeroes-stable (zero-hom-witness a b) f (zero-hom-satisfies a b) (g⁺ (zero-hom-witness a b) f (zeroes-equal (g • zero-hom-witness a b) (g • f) (zero-compose-r g (zero-hom-witness a b) (zero-hom-satisfies a b)) gf₀))

open zeroes public
