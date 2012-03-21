module Sheffield.CategoryTheory-Setoid.Examples.Sets where

open import Function.Equality hiding (_⟶_ ; setoid) renaming (_⇨_ to _⟶_)
open import Level
open import Relation.Binary
open import Relation.Binary.PropositionalEquality hiding (cong)


open import Sheffield.CategoryTheory-Setoid.Categories




Setoids : {ℓ ℓ′ : Level} → Category {suc ℓ ⊔ suc ℓ′} {ℓ ⊔ ℓ′} {ℓ ⊔ ℓ′}
Setoids {ℓ} {ℓ′} = record {
  obj = Setoid ℓ ℓ′ ;
  hom = _⟶_ ;
  id = λ x → id ;
  compose = λ {a} {b} {c} → record {
    _⟨$⟩_ = λ g → record {
      _⟨$⟩_ = λ f → g ∘ f ;
      cong = λ e₁ e₂ → cong g (e₁ e₂) } ;
    cong = λ p E e → p (E e) } ;
  id-l = λ f e → cong f e ; 
  id-r = λ f e → cong f e ; 
  assoc = λ h g f e → cong h (cong g (cong f e)) }

-- We define the category of sets to be a full subcategory of the category of setoids
Sets : {ℓ : Level} → Category {suc ℓ} {ℓ} {ℓ}
Sets {ℓ} = full-subcategory (Setoids {ℓ} {_}) setoid
