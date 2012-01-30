module Categories.Product where

open import Data.Product as Prod using (_,_) renaming (_×_ to _✶_)
open import Level
open import Relation.Binary.PropositionalEquality as PropEq using (_≡_ ; refl)

open import Categories
open import Functors


infixl 7 _×_
_×_ : {ℓ₁ ℓ₂ ℓ′₁ ℓ′₂ : Level} (C₁ : Category {ℓ₁} {ℓ′₁}) (C₂ : Category {ℓ₂} {ℓ′₂}) → Category {ℓ₁ ⊔ ℓ₂} {ℓ′₁ ⊔ ℓ′₂}
makeCat obj₁ hom₁ id₁ compose₁ id-l₁ id-r₁ assoc₁ × makeCat obj₂ hom₂ id₂ compose₂ id-l₂ id-r₂ assoc₂ = makeCat obj hom id compose id-l id-r assoc where
  obj = obj₁ ✶ obj₂
  hom : obj → obj → Set _
  hom (x₁ , x₂) (y₁ , y₂) = hom₁ x₁ y₁ ✶ hom₂ x₂ y₂
  id : (x : obj) → hom x x
  id (x₁ , x₂) = id₁ x₁ , id₂ x₂
  compose : {x y z : obj} → hom y z → hom x y → hom x z
  compose (g₁ , g₂) (f₁ , f₂) = compose₁ g₁ f₁ , compose₂ g₂ f₂
  id-l : {x y : obj} (f : hom x y) → compose (id y) f ≡ f
  id-l (f₁ , f₂) = PropEq.cong₂ _,_ (id-l₁ f₁) (id-l₂ f₂)
  id-r : {x : obj} {y : obj} (f : hom x y) → compose f (id x) ≡ f
  id-r (f₁ , f₂) = PropEq.cong₂ _,_ (id-r₁ f₁) (id-r₂ f₂)
  assoc : {w x y z : obj} (h : hom y z) (g : hom x y) (f : hom w x) → compose h (compose g f) ≡ compose (compose h g) f
  assoc (h₁ , h₂) (g₁ , g₂) (f₁ , f₂) = PropEq.cong₂ _,_ (assoc₁ h₁ g₁ f₁) (assoc₂ h₂ g₂ f₂)


proj₁ : {ℓ₁ ℓ₂ ℓ′₁ ℓ′₂ : Level} {C₁ : Category {ℓ₁} {ℓ′₁}} {C₂ : Category {ℓ₂} {ℓ′₂}} → Functor (C₁ × C₂) C₁
proj₁ = makeFunctor Prod.proj₁ Prod.proj₁ (λ x → refl) (λ g f → refl)

proj₂ : {ℓ₁ ℓ₂ ℓ′₁ ℓ′₂ : Level} {C₁ : Category {ℓ₁} {ℓ′₁}} {C₂ : Category {ℓ₂} {ℓ′₂}} → Functor (C₁ × C₂) C₂
proj₂ = makeFunctor Prod.proj₂ Prod.proj₂ (λ x → refl) (λ g f → refl)

infixl 6 _⋆_
_⋆_ : {ℓ₁ ℓ₂ ℓ₃ ℓ′₁ ℓ′₂ ℓ′₃ : Level} {C : Category {ℓ₁} {ℓ′₁}} {D₁ : Category {ℓ₂} {ℓ′₂}} {D₂ : Category {ℓ₃} {ℓ′₃}} → Functor C D₁ → Functor C D₂ → Functor C (D₁ × D₂) 
F ⋆ G = makeFunctor (λ x → Functor.obj F x , Functor.obj G x) (λ f → Functor.hom F f , Functor.hom G f) (λ x → PropEq.cong₂ _,_ (Functor.id F x) (Functor.id G x)) (λ g f → PropEq.cong₂ _,_ (Functor.compose F g f) (Functor.compose G g f))

×-associator : {ℓ₁ ℓ₂ ℓ₃ ℓ′₁ ℓ′₂ ℓ′₃ : Level} (C₁ : Category {ℓ₁} {ℓ′₁}) (C₂ : Category {ℓ₂} {ℓ′₂}) (C₃ : Category {ℓ₃} {ℓ′₃}) → Functor (C₁ × (C₂ × C₃)) (C₁ × C₂ × C₃)
×-associator C₁ C₂ C₃ = makeFunctor associator associator (λ _ → refl) (λ _ _ → refl) where
  associator : {α β γ : Level} {A : Set α} {B : Set β} {C : Set γ} → A ✶ (B ✶ C) → (A ✶ B) ✶ C
  associator (a , b , c) = (a , b) , c

×-associator⁻¹ : {ℓ₁ ℓ₂ ℓ₃ ℓ′₁ ℓ′₂ ℓ′₃ : Level} (C₁ : Category {ℓ₁} {ℓ′₁}) (C₂ : Category {ℓ₂} {ℓ′₂}) (C₃ : Category {ℓ₃} {ℓ′₃}) → Functor (C₁ × C₂ × C₃) (C₁ × (C₂ × C₃))
×-associator⁻¹ C₁ C₂ C₃ = makeFunctor associator⁻¹ associator⁻¹ (λ _ → refl) (λ _ _ → refl) where
  associator⁻¹ : {α β γ : Level} {A : Set α} {B : Set β} {C : Set γ} → (A ✶ B) ✶ C → A ✶ (B ✶ C)
  associator⁻¹ ((a , b) , c) = a , b , c

infixl 5 _⊕_
_⊕_ : {ℓ₁ ℓ₂ ℓ₃ ℓ₄ ℓ′₁ ℓ′₂ ℓ′₃ ℓ′₄ : Level} {C₁ : Category {ℓ₁} {ℓ′₁}} {C₂ : Category {ℓ₂} {ℓ′₂}} {D₁ : Category {ℓ₃} {ℓ′₃}} {D₂ : Category {ℓ₄} {ℓ′₄}} → Functor C₁ D₁ → Functor C₂ D₂ → Functor (C₁ × C₂) (D₁ × D₂)
_⊕_ {C₁ = C₁} {C₂ = C₂} {D₁ = D₁} {D₂ = D₂} (makeFunctor obj₁ hom₁ id₁ compose₁) (makeFunctor obj₂ hom₂ id₂ compose₂) = makeFunctor obj hom id compose where
  obj : Category.obj (C₁ × C₂) → Category.obj (D₁ × D₂)
  obj (a , b) = obj₁ a , obj₂ b
  hom : {x y : Category.obj (C₁ × C₂)} → Category.hom (C₁ × C₂) x y → Category.hom (D₁ × D₂) (obj x) (obj y)
  hom (f₁ , f₂) = hom₁ f₁ , hom₂ f₂
  id : (x : Category.obj (C₁ × C₂)) → hom (Category.id (C₁ × C₂) x) ≡ Category.id (D₁ × D₂) (obj x)
  id (a , b) = PropEq.cong₂ _,_ (id₁ a) (id₂ b)
  compose : {x y z : Category.obj (C₁ × C₂)} (g : Category.hom (C₁ × C₂) y z) (f : Category.hom (C₁ × C₂) x y) → hom (Category.compose (C₁ × C₂) g f) ≡ Category.compose (D₁ × D₂) (hom g) (hom f)
  compose (g₁ , g₂) (f₁ , f₂) = PropEq.cong₂ _,_ (compose₁ g₁ f₁) (compose₂ g₂ f₂)
