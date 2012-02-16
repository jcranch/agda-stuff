-- The theory of categories. What we implement here is the most naive
-- possible workable version: we have a Set of objects, and a Set of
-- morphisms between any two objects.

-- This is usable for categories where the morphisms are defined
-- inductively, rather than functionally. For example, the category of
-- vector spaces and abstract linear maps will not satisfy this
-- definition, but a "concrete" model built using matrices as linear maps
-- will certainly work.
-- Clearly, most applications to computer algebra will involve categories
-- of this sort.

-- One downside is that this concept of category is not closed under
-- various constructions that involve sets of functions. For example,
-- given any explicit category K, we can define by hand the operation
-- that takes another category C and associates to it the functor
-- category Fun(K,C), but we can't do it uniformly for all K.

-- A more heavy-duty approach would be to use Setoids for the morphisms;
-- this involves a goodly amount more baggage.


module Sheffield.CategoryTheory-Set.Categories where

open import Algebra.Structures
import Data.Product
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

  open Data.Product

  open Category C

  endomorphismMonoid : (x : obj) → IsMonoid _≡_ _•_ (id x)

  endomorphismMonoid x = record {
    isSemigroup = record { 
      isEquivalence = PropEq.isEquivalence ;
      assoc = λ h g f → PropEq.sym (assoc h g f) ;
      ∙-cong = PropEq.cong₂ _•_ } ;
    identity = id-l ,′ id-r }

open endomorphisms public



opposite : {ℓ ℓ′ : Level} → Category {ℓ} {ℓ′} → Category {ℓ} {ℓ′}
opposite (makeCat obj hom id compose id-l id-r assoc) = makeCat obj (flip hom) id (flip compose) id-r id-l (λ f g h → PropEq.sym (assoc h g f))



module Iso {ℓ ℓ′ : Level} (C : Category {ℓ} {ℓ′}) where

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

open Iso


module OppositeIso where

  opposite-iso : {ℓ ℓ′ : Level} {C : Category {ℓ} {ℓ′}} {x y : Category.obj C} {f : Category.hom C x y} → Isomorphism C f → Isomorphism (opposite C) f
  opposite-iso {ℓ} {ℓ′} {C} {x} {y} {f} (makeIso .f f⁻¹ unit counit) = makeIso f f⁻¹ counit unit



-- since epimorphisms are defined as monomorphisms in the opposite category,
-- these facts about monomorphisms will work for epimorphisms just the same.
module monomorphisms {ℓ ℓ′ : Level} (C : Category {ℓ} {ℓ′}) where

  open Category C

  monomorphism : {x y : obj} (f : hom x y) → Set (ℓ ⊔ ℓ′)
  monomorphism {x} {y} f = {w : obj} (g₁ g₂ : hom w x) → f • g₁ ≡ f • g₂ → g₁ ≡ g₂

  monomorphism-compose : {x y z : obj} (g : hom y z) (f : hom x y) → monomorphism g → monomorphism f → monomorphism (g • f)
  monomorphism-compose g f g-mono f-mono h₁ h₂ e = f-mono h₁ h₂ (g-mono (f • h₁) (f • h₂) (PropEq.trans (assoc _ _ _) (PropEq.trans e (PropEq.sym (assoc _ _ _)))))

  monomorphism-cancel : {x y z : obj} (g : hom y z) (f : hom x y) → monomorphism (g • f) → monomorphism f
  monomorphism-cancel g f gf-mono h₁ h₂ e = gf-mono h₁ h₂ (PropEq.trans (PropEq.sym (assoc _ _ _)) (PropEq.trans (PropEq.cong (compose g) e) (assoc _ _ _)))

  isomorphism-monomorphism : {x y : obj} {f : hom x y} (f-iso : Isomorphism C f) → monomorphism f
  isomorphism-monomorphism {x} {y} (makeIso f f⁻¹ unit counit) g₁ g₂ e = begin
    g₁
      ≡⟨ PropEq.sym (id-l g₁) ⟩
    (id x) • g₁
      ≡⟨ PropEq.cong (λ α → α • g₁) (PropEq.sym unit) ⟩
    (f⁻¹ • f) • g₁
      ≡⟨ PropEq.sym (assoc _ _ _) ⟩
    f⁻¹ • (f • g₁)
      ≡⟨ PropEq.cong (λ α → f⁻¹ • α) e ⟩
    f⁻¹ • (f • g₂)
      ≡⟨ assoc _ _ _ ⟩
    (f⁻¹ • f) • g₂
      ≡⟨ PropEq.cong (λ α → α • g₂) unit ⟩
    (id x) • g₂
      ≡⟨ id-l g₂ ⟩
    g₂ ∎

open monomorphisms public

epimorphism : {ℓ ℓ′ : Level} (C : Category {ℓ} {ℓ′}) {x y : Category.obj C} (f : Category.hom C x y) → Set (ℓ ⊔ ℓ′)
epimorphism C f = monomorphism (opposite C) f



