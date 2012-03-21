module Sheffield.CategoryTheory-Setoid.Examples.MonoidCategory where

open import Algebra
open import Data.Product
open import Data.Unit hiding (setoid)
open import Level
open import Relation.Binary

open import Sheffield.CategoryTheory-Setoid.Categories


monoid-category : {ℓ ℓ′ : Level} (M : Monoid ℓ ℓ′) → Category {zero} {ℓ} {ℓ′}
monoid-category M = record {
  obj = ⊤ ;
  hom = λ _ _ → setoid ;
  id = λ _ → ε ;
  compose = record {
    _⟨$⟩_ = λ x → record {
      _⟨$⟩_ = λ y → x ∙ y ;
      cong = ∙-cong refl } ;
    cong = λ e₁ e₂ → ∙-cong e₁ e₂ } ;
  id-l = λ x → proj₁ identity x ;
  id-r = λ x → proj₂ identity x ;
  assoc = assoc } where
  open Monoid M
  
