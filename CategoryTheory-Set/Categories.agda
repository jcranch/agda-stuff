module Categories where

open import Algebra.Structures
open import Level
open import Function using (flip)
open import Relation.Binary.PropositionalEquality as PropEq using (_≡_)
open PropEq.≡-Reasoning



record Category {ℓ ℓ′ : Level} : Set (suc ℓ ⊔ suc ℓ′) where
  constructor makeCat
  infixl 7 _•_
  field
    obj : Set ℓ
    hom : obj  → obj → Set ℓ′
    id : (x : obj) → hom x x
    compose : {x y z : obj} → hom y z → hom x y → hom x z
    id-l : {x y : obj} (f : hom x y) → compose (id y) f ≡ f
    id-r : {x y : obj} (f : hom x y) → compose f (id x) ≡ f
    assoc : {w x y z : obj} (h : hom y z) (g : hom x y) (f : hom w x) → compose h (compose g f) ≡ compose (compose h g) f
  _•_ : {x y z : obj} → hom y z → hom x y → hom x z
  g • f = compose g f



module endomorphisms {ℓ ℓ′ : Level} {C : Category {ℓ} {ℓ′}} where

  open import Data.Product

  open Category C

  endomorphismMonoid : (x : obj) → IsMonoid _≡_ _•_ (id x)

  endomorphismMonoid x = record {
    isSemigroup = record { 
      isEquivalence = PropEq.isEquivalence ;
      assoc = λ h g f → PropEq.sym (assoc h g f) ;
      ∙-cong = PropEq.cong₂ _•_ } ;
    identity = id-l ,′ id-r }

open endomorphisms public



module Iso {ℓ ℓ′ : Level} {C : Category {ℓ} {ℓ′}} where

  open Category C

  data Isomorphism {x y : obj} : (f : hom x y) → Set ℓ′ where
    makeIso : (f : hom x y) (f⁻¹ : hom y x) (unit : f⁻¹ • f ≡ id x) (counit : f • f⁻¹ ≡ id y) → Isomorphism f

  data Isomorphic (x y : obj) : Set ℓ′ where
    makeIso' : (f : hom x y) (i : Isomorphism f) → Isomorphic x y

  left-right-inverses-agree : {x y : obj} {f : hom x y} {fl fr : hom y x} → fl • f ≡ id x → f • fr ≡ id y → fl ≡ fr
  left-right-inverses-agree {x} {y} {f} {fl} {fr} fli fri = begin
    fl
      ≡⟨ PropEq.sym (Category.id-r C fl) ⟩
    fl • (id y)
      ≡⟨ PropEq.sym (PropEq.cong (λ a → fl • a) fri) ⟩
    fl • (f • fr)
      ≡⟨ Category.assoc C fl f fr ⟩
    (fl • f) • fr
      ≡⟨ PropEq.cong (λ a → a • fr) fli ⟩
    (id x) • fr
      ≡⟨ Category.id-l C fr ⟩
    fr ∎

  double-cancellation : {x y z : obj}
                        {f : hom x y} {f⁻¹ : hom y x}
                        {g : hom y z} {g⁻¹ : hom z y} →
                        f⁻¹ • f ≡ id x →
                        g⁻¹ • g ≡ id y →
                        (f⁻¹ • g⁻¹) • (g • f) ≡ id x
  double-cancellation {x} {y} {z} {f} {f⁻¹} {g} {g⁻¹} ef eg = begin
    (f⁻¹ • g⁻¹) • (g • f)
      ≡⟨ assoc (f⁻¹ • g⁻¹) g f ⟩
    ((f⁻¹ • g⁻¹) • g) • f
      ≡⟨ PropEq.cong (λ a → a • f) (PropEq.sym (assoc f⁻¹ g⁻¹ g)) ⟩
    (f⁻¹ • (g⁻¹ • g)) • f
      ≡⟨ PropEq.cong (λ a → (f⁻¹ • a) • f) eg ⟩
    (f⁻¹ • (id y)) • f
      ≡⟨ PropEq.cong (λ a → a • f) (id-r f⁻¹) ⟩
    f⁻¹ • f
      ≡⟨ ef ⟩
    id x ∎

  inverse : {x y : obj} {f : hom x y} → Isomorphism f → hom y x
  inverse {x} {y} {f} (makeIso .f f⁻¹ unit counit) = f⁻¹

  inverse-unique : {x y : obj} (f : hom x y) (i₁ i₂ : Isomorphism f) → inverse i₁ ≡ inverse i₂
  inverse-unique f (makeIso .f _ unit _) (makeIso .f _ _ counit') = left-right-inverses-agree unit counit'

  refl : (x : obj) → Isomorphism (id x)
  refl x = makeIso (id x) (id x) (id-l (id x)) (id-r (id x))

  sym : {x y : obj} {f : hom x y} (i : Isomorphism f) → Isomorphism (inverse i)
  sym {x} {y} {f} (makeIso .f f⁻¹ unit counit) = makeIso f⁻¹ f counit unit

  trans : {x y z : obj} {g : hom y z} {f : hom x y} → Isomorphism g → Isomorphism f → Isomorphism (g • f)
  trans {x} {y} {z} {g} {f} (makeIso .g g⁻¹ unit-g counit-g) (makeIso .f f⁻¹ unit-f counit-f) = makeIso (g • f) (f⁻¹ • g⁻¹) (double-cancellation unit-f unit-g) (double-cancellation counit-g counit-f)


opposite : {ℓ ℓ′ : Level} → Category {ℓ} {ℓ′} → Category {ℓ} {ℓ′}
opposite (makeCat obj hom id compose id-l id-r assoc) = makeCat obj (flip hom) id (flip compose) id-r id-l (λ f g h → PropEq.sym (assoc h g f))



module OppositeIso where

  open Iso

  opposite-iso : {ℓ ℓ′ : Level} {C : Category {ℓ} {ℓ′}} {x y : Category.obj C} {f : Category.hom C x y} → Isomorphism {_} {_} {C} f → Isomorphism {_} {_} {opposite C} f
  opposite-iso {ℓ} {ℓ′} {C} {x} {y} {f} (makeIso .f f⁻¹ unit counit) = makeIso f f⁻¹ counit unit
