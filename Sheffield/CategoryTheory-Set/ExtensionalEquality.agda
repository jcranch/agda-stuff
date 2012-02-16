module Sheffield.CategoryTheory-Set.ExtensionalEquality where

-- Not sure this does any good.
-- Need a propositional and a heterogeneous version

open import Function
open import Level
open import Relation.Binary.PropositionalEquality as PropEq
open import Relation.Binary.HeterogeneousEquality as HetrEq


infix 4 _≣_

_≣_ : {α β : Level} {A : Set α} {B : Set β} → (A → B) → (A → B) → Set (α ⊔ β)
_≣_ {_} {_} {A} {B} F G = (a : A) → F a ≡ G a

≣-refl : {α β : Level} {A : Set α} {B : Set β} (F : A → B) → F ≣ F
≣-refl F a = refl

≣-sym : {α β : Level} {A : Set α} {B : Set β} {F₁ F₂ : A → B} → F₁ ≣ F₂ → F₂ ≣ F₁
≣-sym e a = PropEq.sym (e a)

≣-trans : {α β : Level} {A : Set α} {B : Set β} {F₁ F₂ F₃ : A → B} → F₁ ≣ F₂ → F₂ ≣ F₃ → F₁ ≣ F₃
≣-trans e₁₂ e₂₃ a = PropEq.trans (e₁₂ a) (e₂₃ a)

≣-composition : {α β γ : Level} {A : Set α} {B : Set β} {C : Set γ} {F₁ F₂ : A → B} {G₁ G₂ : B → C} → G₁ ≣ G₂ → F₁ ≣ F₂ → (G₁ ∘ F₁) ≣ (G₂ ∘ F₂)
≣-composition {_} {_} {_} {_} {_} {_} {F₁} {F₂} {G₁} {G₂} g f a = PropEq.subst (λ z → G₁ (F₁ a) ≡ G₂ z) (f a) (g (F₁ a))


infix 4 _≣′_

_≣′_ : {α β : Level} {A : Set α} {B B′ : Set β} → (A → B) → (A → B′) → Set α
_≣′_ {_} {_} {A} {_} F G = (a : A) → F a ≅ G a

≣′-refl : {α β : Level} {A : Set α} {B : Set β} (F : A → B) → F ≣′ F
≣′-refl F a = refl

≣′-sym : {α β : Level} {A : Set α} {B : Set β} {F₁ F₂ : A → B} → F₁ ≣′ F₂ → F₂ ≣′ F₁
≣′-sym e a = HetrEq.sym (e a)

≣′-trans : {α β : Level} {A : Set α} {B : Set β} {F₁ F₂ F₃ : A → B} → F₁ ≣′ F₂ → F₂ ≣′ F₃ → F₁ ≣′ F₃
≣′-trans e₁₂ e₂₃ a = HetrEq.trans (e₁₂ a) (e₂₃ a)

≣′-composition : {α β γ : Level} {A : Set α} {B : Set β} {C : Set γ} {F₁ F₂ : A → B} {G₁ G₂ : B → C} → G₁ ≣′ G₂ → F₁ ≣′ F₂ → (G₁ ∘ F₁) ≣′ (G₂ ∘ F₂)
≣′-composition {_} {_} {_} {_} {_} {_} {F₁} {F₂} {G₁} {G₂} g f a = HetrEq.subst (λ z → G₁ (F₁ a) ≅ G₂ z) (f a) (g (F₁ a))
