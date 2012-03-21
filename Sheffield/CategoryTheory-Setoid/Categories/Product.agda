module Sheffield.CategoryTheory-Setoid.Categories.Product where

open import Data.Product renaming (_×_ to _✶_ ; proj₁ to proj⁺₁ ; proj₂ to proj⁺₂)
open import Function.Equality hiding (id ; _⟶_) renaming (_⇨_ to _⟶_)
open import Level
open import Relation.Binary

open import Sheffield.CategoryTheory-Setoid.Categories
open import Sheffield.CategoryTheory-Setoid.Categories.Diagrams using (point)
open import Sheffield.CategoryTheory-Setoid.Functors
open import Sheffield.CategoryTheory-Setoid.SetoidFunction
open import Sheffield.CategoryTheory-Setoid.SetoidProduct hiding (_⊕_ ; proj₁ ; proj₂) renaming (_×_ to _★_)


infixr 7 _×_
_×_ : {ℓ₁ ℓ′₁ ℓ″₁ ℓ₂ ℓ′₂ ℓ″₂ : Level} (C₁ : Category {ℓ₁} {ℓ′₁} {ℓ″₁}) (C₂ : Category {ℓ₂} {ℓ′₂} {ℓ″₂}) → Category {ℓ₁ ⊔ ℓ₂} {ℓ′₁ ⊔ ℓ′₂} {ℓ″₁ ⊔ ℓ″₂}
makeCat obj₁ hom₁ id₁ compose₁ id-l₁ id-r₁ assoc₁ × makeCat obj₂ hom₂ id₂ compose₂ id-l₂ id-r₂ assoc₂ = makeCat obj hom id compose id-l id-r assoc where
  obj = obj₁ ✶ obj₂
  hom : obj → obj → Setoid _ _
  hom (x₁ , x₂) (y₁ , y₂) = hom₁ x₁ y₁ ★ hom₂ x₂ y₂
  homset : obj → obj → Set _
  homset x y = Setoid.Carrier (hom x y)
  infix 4 _≈_
  _≈_ : {x y : obj} → Rel (homset x y) _
  _≈_ {x} {y} = Setoid._≈_ (hom x y)
  id : (x : obj) → Γ (hom x x)
  id (x₁ , x₂) = id₁ x₁ , id₂ x₂
  compose : {x y z : obj} → Γ (hom y z ⟶ hom x y ⟶ hom x z)
  compose = record {
    _⟨$⟩_ = λ g → record {
      _⟨$⟩_ = λ f → compose₁ ⟨$⟩ (proj⁺₁ g) ⟨$⟩ (proj⁺₁ f) , compose₂ ⟨$⟩ (proj⁺₂ g) ⟨$⟩ (proj⁺₂ f) ;
      cong = λ e → cong compose₁ (Setoid.refl (hom₁ _ _)) (proj⁺₁ e) , cong compose₂ (Setoid.refl (hom₂ _ _)) (proj⁺₂ e) } ;
    cong = λ e₁ e₂ → cong compose₁ (proj⁺₁ e₁) (proj⁺₁ e₂) , cong compose₂ (proj⁺₂ e₁) (proj⁺₂ e₂) }
  infixl 7 _•_
  _•_ : {x y z : obj} → homset y z → homset x y → homset x z
  g • f = compose ⟨$⟩ g ⟨$⟩ f
  id-l : {x y : obj} (f : homset x y) → id y • f ≈ f
  id-l (f₁ , f₂) = id-l₁ f₁ , id-l₂ f₂
  id-r : {x : obj} {y : obj} (f : homset x y) → f • id x ≈ f
  id-r (f₁ , f₂) = id-r₁ f₁ , id-r₂ f₂
  assoc : {w x y z : obj} (h : homset y z) (g : homset x y) (f : homset w x) → (h • g) • f ≈ h • (g • f)
  assoc (h₁ , h₂) (g₁ , g₂) (f₁ , f₂) = assoc₁ h₁ g₁ f₁ , assoc₂ h₂ g₂ f₂


proj₁ : {ℓ₁ ℓ′₁ ℓ″₁ ℓ₂ ℓ′₂ ℓ″₂ : Level} {C₁ : Category {ℓ₁} {ℓ′₁} {ℓ″₁}} {C₂ : Category {ℓ₂} {ℓ′₂} {ℓ″₂}} → Functor (C₁ × C₂) C₁
proj₁ {C₁ = C₁} {C₂ = C₂} = record {
  obj = proj⁺₁ ;
  hom = record {
    _⟨$⟩_ = proj⁺₁ ;
    cong = proj⁺₁ } ;
  compose = λ g f → ≈-refl ;
  id = λ x → ≈-refl }
  where open Category C₁

proj₂ : {ℓ₁ ℓ′₁ ℓ″₁ ℓ₂ ℓ′₂ ℓ″₂ : Level} {C₁ : Category {ℓ₁} {ℓ′₁} {ℓ″₁}} {C₂ : Category {ℓ₂} {ℓ′₂} {ℓ″₂}} → Functor (C₁ × C₂) C₂
proj₂ {C₁ = C₁} {C₂ = C₂} = record {
  obj = proj⁺₂ ;
  hom = record {
    _⟨$⟩_ = proj⁺₂ ;
    cong = proj⁺₂ } ;
  compose = λ g f → ≈-refl ;
  id = λ x → ≈-refl }
  where open Category C₂


infixl 6 _⋆_
_⋆_ : {ℓ₁ ℓ′₁ ℓ″₁ ℓ₂ ℓ′₂ ℓ″₂ ℓ₃ ℓ′₃ ℓ″₃ : Level} {C : Category {ℓ₁} {ℓ′₁} {ℓ″₁}} {D₁ : Category {ℓ₂} {ℓ′₂} {ℓ″₂}} {D₂ : Category {ℓ₃} {ℓ′₃} {ℓ″₃}} → Functor C D₁ → Functor C D₂ → Functor C (D₁ × D₂) 
F ⋆ G = record {
  obj = λ x → Functor.obj F x , Functor.obj G x ;
  hom = record {
    _⟨$⟩_ = λ f → Functor.homsets F f , Functor.homsets G f ;
    cong = λ f → Functor.hom-cong F f , Functor.hom-cong G f } ;
  id = λ x → Functor.id F x , Functor.id G x ;
  compose = λ g f → Functor.compose F g f , Functor.compose G g f }


×-commutator : {ℓ₁ ℓ′₁ ℓ″₁ ℓ₂ ℓ′₂ ℓ″₂ : Level} (C₁ : Category {ℓ₁} {ℓ′₁} {ℓ″₁}) (C₂ : Category {ℓ₂} {ℓ′₂} {ℓ″₂}) → Functor (C₁ × C₂) (C₂ × C₁)
×-commutator C₁ C₂ = record {
  obj = swap ;
  hom = record {
    _⟨$⟩_ = swap ;
    cong = swap } ;
  id = λ _ → (Category.≈-refl C₂ ,′ Category.≈-refl C₁) ;
  compose = λ _ _ → (Category.≈-refl C₂ ,′ Category.≈-refl C₁) }


×-associator : {ℓ₁ ℓ′₁ ℓ″₁ ℓ₂ ℓ′₂ ℓ″₂ ℓ₃ ℓ′₃ ℓ″₃ : Level} (C₁ : Category {ℓ₁} {ℓ′₁} {ℓ″₁}) (C₂ : Category {ℓ₂} {ℓ′₂} {ℓ″₂}) (C₃ : Category {ℓ₃} {ℓ′₃} {ℓ″₃}) → Functor ((C₁ × C₂) × C₃) (C₁ × (C₂ × C₃))
×-associator C₁ C₂ C₃ = record {
  obj = associator ;
  hom = associator′ {A = Category.hom C₁ _ _} {B = Category.hom C₂ _ _} {C = Category.hom C₃ _ _} ;
  id = λ x → Category.≈-refl C₁ , Category.≈-refl C₂ , Category.≈-refl C₃ ;
  compose = λ g f → Category.≈-refl C₁ , Category.≈-refl C₂ , Category.≈-refl C₃ } where
  associator : {α β γ : Level} {A : Set α} {B : Set β} {C : Set γ} → (A ✶ B) ✶ C → A ✶ (B ✶ C)
  associator ((a , b) , c) = a , b , c
  associator′ : {α α′ β β′ γ γ′ : Level} {A : Setoid α α′} {B : Setoid β β′} {C : Setoid γ γ′} → Γ ((A ★ B) ★ C ⟶ A ★ (B ★ C))
  associator′ = record {
    _⟨$⟩_ = associator ;
    cong = associator }


×-associator⁻¹ : {ℓ₁ ℓ′₁ ℓ″₁ ℓ₂ ℓ′₂ ℓ″₂ ℓ₃ ℓ′₃ ℓ″₃ : Level} (C₁ : Category {ℓ₁} {ℓ′₁} {ℓ″₁}) (C₂ : Category {ℓ₂} {ℓ′₂} {ℓ″₂}) (C₃ : Category {ℓ₃} {ℓ′₃} {ℓ″₃}) → Functor (C₁ × (C₂ × C₃)) ((C₁ × C₂) × C₃)
×-associator⁻¹ C₁ C₂ C₃ = record {
  obj = associator⁻¹ ;
  hom = associator⁻¹′ {A = Category.hom C₁ _ _} {B = Category.hom C₂ _ _} {C = Category.hom C₃ _ _} ;
  id = λ x → (Category.≈-refl C₁ , Category.≈-refl C₂) , Category.≈-refl C₃ ;
  compose = λ g f → (Category.≈-refl C₁ , Category.≈-refl C₂) , Category.≈-refl C₃ } where
  associator⁻¹ : {α β γ : Level} {A : Set α} {B : Set β} {C : Set γ} → A ✶ (B ✶ C) → (A ✶ B) ✶ C
  associator⁻¹ (a , b , c) = (a , b) , c
  associator⁻¹′ : {α α′ β β′ γ γ′ : Level} {A : Setoid α α′} {B : Setoid β β′} {C : Setoid γ γ′} → Γ (A ★ (B ★ C) ⟶ (A ★ B) ★ C)
  associator⁻¹′ = record {
    _⟨$⟩_ = associator⁻¹ ;
    cong = associator⁻¹ }


infixl 5 _⊕_
_⊕_ : {ℓ₁ ℓ′₁ ℓ″₁ ℓ₂ ℓ′₂ ℓ″₂ ℓ₃ ℓ′₃ ℓ″₃ ℓ₄ ℓ′₄ ℓ″₄ : Level} {C₁ : Category {ℓ₁} {ℓ′₁} {ℓ″₁}} {C₂ : Category {ℓ₂} {ℓ′₂} {ℓ″₂}} {D₁ : Category {ℓ₃} {ℓ′₃} {ℓ″₃}} {D₂ : Category {ℓ₄} {ℓ′₄} {ℓ″₄}} → Functor C₁ D₁ → Functor C₂ D₂ → Functor (C₁ × C₂) (D₁ × D₂)
_⊕_ {C₁ = C₁} {C₂ = C₂} F G = (F ⊙ proj₁ {C₁ = C₁} {C₂ = C₂}) ⋆ (G ⊙ proj₂ {C₁ = C₁} {C₂ = C₂})