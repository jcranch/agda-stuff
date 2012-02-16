module Sheffield.CategoryTheory-Set.Under-Over where

open import Data.Product
open import Level
open import Relation.Binary.PropositionalEquality

open import Sheffield.CategoryTheory-Set.Categories


module overcategory {ℓ ℓ′ : Level} (C : Category {ℓ} {ℓ′}) (y : Category.obj C) where

  open Category C

  private
    obj′ : Set (ℓ ⊔ ℓ′)
    obj′ = Σ obj (λ x → hom x y)

    hom′ : obj′ → obj′ → Set ℓ′
    hom′ (x₁ , f₁) (x₂ , f₂) = Σ (hom x₁ x₂) (λ f → f₂ • f ≡ f₁ )

  ≡-hom : {x y : obj′} (F₁ F₂ : hom′ x y) → proj₁ F₁ ≡ proj₁ F₂ → F₁ ≡ F₂
  ≡-hom (f , e₁) (.f , e₂) refl = cong (λ ε → (f , ε)) (proof-irrelevance e₁ e₂)

  private
    id′ : (x : obj′) → hom′ x x
    id′ (x , f) = (id x , id-r f)

    compose′ : {x y z : obj′} → hom′ y z → hom′ x y → hom′ x z
    compose′ {(_ , h₀)} {(_ , h₁)} {(_ , h₂)} (g , j) (f , i) = (g • f , k) where
      k = begin
        h₂ • (g • f)
          ≡⟨ assoc h₂ g f ⟩
        h₂ • g • f
          ≡⟨ cong (λ a → a • f) j ⟩
        h₁ • f
          ≡⟨ i ⟩
        h₀ ∎ where open ≡-Reasoning

    id-l′ : {x₁ x₂ : obj′} (f : hom′ x₁ x₂) → compose′ (id′ x₂) f ≡ f
    id-l′ {x₁} {x₂} f = ≡-hom (compose′ (id′ x₂) f) f (id-l (proj₁ f)) 

    id-r′ : {x₁ x₂ : obj′} (f : hom′ x₁ x₂) → compose′ f (id′ x₁) ≡ f
    id-r′ {x₁} {x₂} f = ≡-hom (compose′ f (id′ x₁)) f (id-r (proj₁ f)) 

    assoc′ : {x₁ x₂ x₃ x₄ : obj′} (h : hom′ x₃ x₄) (g : hom′ x₂ x₃) (f : hom′ x₁ x₂) →
      compose′ h (compose′ g f) ≡ compose′ (compose′ h g) f
    assoc′ h g f = ≡-hom (compose′ h (compose′ g f)) (compose′ (compose′ h g) f) (assoc (proj₁ h) (proj₁ g) (proj₁ f))

  Overcategory = makeCat obj′ hom′ id′ compose′ id-l′ id-r′ assoc′

open overcategory public

infix 6 _//_
_//_ : {ℓ ℓ′ : Level} (C : Category {ℓ} {ℓ′}) (y : Category.obj C) → Category {ℓ ⊔ ℓ′} {ℓ′}
_//_ {ℓ} {ℓ′} C y = Overcategory C y
  
Undercategory : {ℓ ℓ′ : Level} (C : Category {ℓ} {ℓ′}) (x : Category.obj C) → Category {ℓ ⊔ ℓ′} {ℓ′}
Undercategory C x = opposite (Overcategory (opposite C) x)

infix 6 _\\_
_\\_ : {ℓ ℓ′ : Level} (C : Category {ℓ} {ℓ′}) (x : Category.obj C) → Category {ℓ ⊔ ℓ′} {ℓ′}
_\\_ {ℓ} {ℓ′} C x = Undercategory C x
