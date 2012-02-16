-- Some useful finite categories

module Sheffield.CategoryTheory-Set.Categories.Diagrams where

open import Data.Empty
open import Data.Unit
open import Data.Sum renaming (_⊎_ to _+_)
open import Level
open import Relation.Binary.PropositionalEquality as PropEq using (_≡_ ; refl)

open import Sheffield.CategoryTheory-Set.Categories
open import Sheffield.CategoryTheory-Set.Categories.Join
open import Sheffield.CategoryTheory-Set.Categories.Parallel
open import Sheffield.CategoryTheory-Set.Categories.Sum
open import Sheffield.CategoryTheory-Set.Functors
open import Sheffield.CategoryTheory-Set.NaturalTransformations



∅ : Category {zero} {zero}
∅ = makeCat ⊥ ⊥-elim (λ ()) (λ {x} {y} → λ {}) (λ {x} → λ {}) (λ {x} → λ {}) (λ {w} {x} {y} → λ {})

∅-functor : {ℓ₁ ℓ′₁ : Level} {C : Category {ℓ₁} {ℓ′₁}} → Functor ∅ C
∅-functor = makeFunctor (λ ()) (λ {x} → λ {}) (λ ()) (λ {x} {y} → λ {})

∅-nat-trans : {ℓ₁ ℓ′₁ : Level} {C : Category {ℓ₁} {ℓ′₁}} {F G : Functor ∅ C} → NatTrans F G
∅-nat-trans = makeNatTrans (λ ()) (λ {x} → λ {})



point : Category {zero} {zero}
point = makeCat ⊤ (λ _ _ → ⊤) (λ _ → tt) (λ _ _ → tt) (λ _ → refl) (λ _ → refl) (λ _ _ _ → refl)


2points : Category {zero} {zero}
2points = point ⊎ point

2points-functor : {ℓ₁ ℓ′₁ : Level} {C : Category {ℓ₁} {ℓ′₁}} (α β : Category.obj C) → Functor 2points C
2points-functor {C = C} α β = ⊎-functor (constFunctor point C α) (constFunctor point C β)

2points-nat-trans : {ℓ₁ ℓ′₁ : Level} {C : Category {ℓ₁} {ℓ′₁}} (F G : Functor 2points C) (f : Category.hom C (Functor.obj F (inj₁ tt)) (Functor.obj G (inj₁ tt))) (g : Category.hom C (Functor.obj F (inj₂ tt)) (Functor.obj G (inj₂ tt))) → NatTrans F G
2points-nat-trans {C = C} F G f g = makeNatTrans o c where
  o : (x : Category.obj 2points) → Category.hom C (Functor.obj F x) (Functor.obj G x)
  o (inj₁ tt) = f
  o (inj₂ tt) = g
  c : {x y : Category.obj 2points} (h : Category.hom 2points x y) → Category.compose C (o y) (Functor.hom F h) ≡ Category.compose C (Functor.hom G h) (o x)
  c (ssi₁ tt tt tt) = naturality-for-identities F G (inj₁ tt) f
  c (ssi₂ tt tt tt) = naturality-for-identities F G (inj₂ tt) g


↗↖ : Category {zero} {zero}
↗↖ = 2points ✫ point

↗↖-functor : {ℓ₁ ℓ′₁ : Level} {C : Category {ℓ₁} {ℓ′₁}} {a₁ a₂ b : Category.obj C} (f₁ : Category.hom C a₁ b) (f₂ : Category.hom C a₂ b) → Functor ↗↖ C
↗↖-functor {_} {_} {C} {a₁} {a₂} {b} f₁ f₂ = makeFunctor obj hom id compose where
  obj : Category.obj ↗↖ → Category.obj C
  obj (inj₁ (inj₁ tt)) = a₁
  obj (inj₁ (inj₂ tt)) = a₂
  obj (inj₂ tt) = b
  hom : {x y : Category.obj ↗↖} → Category.hom ↗↖ x y → Category.hom C (obj x) (obj y)
  hom (j-inj₁ .(inj₁ tt) .(inj₁ tt) (ssi₁ tt tt tt)) = Category.id C a₁
  hom (j-inj₁ .(inj₂ tt) .(inj₂ tt) (ssi₂ tt tt tt)) = Category.id C a₂
  hom (j-inj₂ tt tt tt) = Category.id C b
  hom (j-inj₁₂ (inj₁ tt) tt) = f₁
  hom (j-inj₁₂ (inj₂ tt) tt) = f₂
  id : (x : Category.obj ↗↖) → hom (Category.id ↗↖ x) ≡ Category.id C (obj x)
  id (inj₁ (inj₁ tt)) = refl
  id (inj₁ (inj₂ tt)) = refl
  id (inj₂ tt) = refl
  compose : {x y z : Category.obj ↗↖} (g : Category.hom ↗↖ y z) (f : Category.hom ↗↖ x y) → hom (Category.compose ↗↖ g f) ≡ Category.compose C (hom g) (hom f)
  compose (j-inj₁ .(inj₁ tt) .(inj₁ tt) (ssi₁ tt tt tt)) (j-inj₁ .(inj₁ tt) .(inj₁ tt) (ssi₁ tt .tt tt)) = PropEq.sym (Category.id-r C _)
  compose (j-inj₁ .(inj₂ tt) .(inj₂ tt) (ssi₂ tt tt tt)) (j-inj₁ .(inj₂ tt) .(inj₂ tt) (ssi₂ tt .tt tt)) = PropEq.sym (Category.id-r C _)
  compose (j-inj₂ tt tt tt) (j-inj₂ tt .tt tt) = PropEq.sym (Category.id-r C _)
  compose (j-inj₂ tt tt tt) (j-inj₁₂ (inj₁ tt) .tt) = PropEq.sym (Category.id-l C _)
  compose (j-inj₂ tt tt tt) (j-inj₁₂ (inj₂ tt) .tt) = PropEq.sym (Category.id-l C _)
  compose (j-inj₁₂ .(inj₁ tt) tt) (j-inj₁ .(inj₁ tt) .(inj₁ tt) (ssi₁ tt tt tt)) = PropEq.sym (Category.id-r C _)
  compose (j-inj₁₂ .(inj₂ tt) tt) (j-inj₁ .(inj₂ tt) .(inj₂ tt) (ssi₂ tt tt tt)) = PropEq.sym (Category.id-r C _)

↗↖-nat-trans : {ℓ₁ ℓ′₁ : Level} {C : Category {ℓ₁} {ℓ′₁}} (F G : Functor ↗↖ C)
  (f₁₁ : Category.hom C (Functor.obj F (inj₁ (inj₁ tt))) (Functor.obj G (inj₁ (inj₁ tt))))
  (f₁₂ : Category.hom C (Functor.obj F (inj₁ (inj₂ tt))) (Functor.obj G (inj₁ (inj₂ tt))))
  (f₂ : Category.hom C (Functor.obj F (inj₂ tt)) (Functor.obj G (inj₂ tt))) →
  Category.compose C f₂ (Functor.hom F (j-inj₁₂ (inj₁ tt) tt)) ≡ Category.compose C (Functor.hom G (j-inj₁₂ (inj₁ tt) tt)) f₁₁ →
  Category.compose C f₂ (Functor.hom F (j-inj₁₂ (inj₂ tt) tt)) ≡ Category.compose C (Functor.hom G (j-inj₁₂ (inj₂ tt) tt)) f₁₂ → NatTrans F G
↗↖-nat-trans {C = C} F G f₁₁ f₁₂ f₂ e₁ e₂ = makeNatTrans component naturality where
  component : (x : Category.obj ↗↖) → Category.hom C (Functor.obj F x) (Functor.obj G x)
  component (inj₁ (inj₁ tt)) = f₁₁
  component (inj₁ (inj₂ tt)) = f₁₂
  component (inj₂ tt) = f₂
  naturality : {x y : Category.obj ↗↖} (f : Category.hom ↗↖ x y) → Category.compose C (component y) (Functor.hom F f) ≡ Category.compose C (Functor.hom G f) (component x)
  naturality (j-inj₁ .(inj₁ tt) .(inj₁ tt) (ssi₁ tt tt tt)) = naturality-for-identities F G (inj₁ (inj₁ tt)) f₁₁
  naturality (j-inj₁ .(inj₂ tt) .(inj₂ tt) (ssi₂ tt tt tt)) = naturality-for-identities F G (inj₁ (inj₂ tt)) f₁₂
  naturality (j-inj₂ tt tt tt) = naturality-for-identities F G (inj₂ tt) f₂
  naturality (j-inj₁₂ (inj₁ tt) tt) = e₁
  naturality (j-inj₁₂ (inj₂ tt) tt) = e₂


↙↘ : Category {zero} {zero}
↙↘ = point ✫ 2points


⇉ : Category {zero} {zero}
⇉ = parallels (⊤ + ⊤)

⇉-functor : {ℓ₁ ℓ′₁ : Level} {C : Category {ℓ₁} {ℓ′₁}} {s t : Category.obj C} (f g : Category.hom C s t) → Functor ⇉ C
⇉-functor {C = C} {s} {t} f g = parallels-functor h where
  h : ⊤ + ⊤ → Category.hom C s t
  h (inj₁ tt) = f
  h (inj₂ tt) = g

⇉-nat-trans : {ℓ₁ ℓ′₁ : Level} {C : Category {ℓ₁} {ℓ′₁}} (F G : Functor ⇉ C)
  (s₁ : Category.hom C (Functor.obj F source) (Functor.obj G source))
  (t₁ : Category.hom C (Functor.obj F target) (Functor.obj G target)) →
  Category.compose C t₁ (Functor.hom F (parallel-map (inj₁ tt))) ≡ Category.compose C (Functor.hom G (parallel-map (inj₁ tt))) s₁ →
  Category.compose C t₁ (Functor.hom F (parallel-map (inj₂ tt))) ≡ Category.compose C (Functor.hom G (parallel-map (inj₂ tt))) s₁ →
  NatTrans F G
⇉-nat-trans {C = C} F G s₁ t₁ e₁ e₂ = parallels-nat-trans F G s₁ t₁ h where
  h : (a : ⊤ + ⊤) → Category.compose C t₁ (Functor.hom F (parallel-map a)) ≡ Category.compose C (Functor.hom G (parallel-map a)) s₁
  h (inj₁ x) = e₁
  h (inj₂ y) = e₂