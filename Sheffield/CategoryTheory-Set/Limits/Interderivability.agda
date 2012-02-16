module Sheffield.CategoryTheory-Set.Limits.Interderivability where

open import Data.Product using (_×_)
open import Data.Sum
open import Data.Unit
open import Function
open import Level
open import Relation.Binary.PropositionalEquality

open import Sheffield.CategoryTheory-Set.Categories
open import Sheffield.CategoryTheory-Set.Categories.Diagrams
open import Sheffield.CategoryTheory-Set.Functors
open import Sheffield.CategoryTheory-Set.Limits.Equaliser
open import Sheffield.CategoryTheory-Set.Limits.Product
open import Sheffield.CategoryTheory-Set.Limits.Pullback
open import Sheffield.CategoryTheory-Set.Limits.Terminal hiding (exists-to-1 ; unique-to-1)
open import Sheffield.CategoryTheory-Set.Misc


module general-context {ℓ₁ ℓ′₁ : Level} (C : Category {ℓ₁} {ℓ′₁}) where

  open Category C

  module pullback-to-terminal {t x y x×y : obj} (term : IsTerminal-lowbrow C t) (p₁ : hom x×y x) (p₂ : hom x×y y) (t₁ : hom x t) (t₂ : hom y t) (e : t₁ • p₁ ≡ t₂ • p₂) where

    open IsTerminal-lowbrow term

    product-as-pullback-to-terminal : (pb : IsPullback-lowbrow C t₁ t₂ p₁ p₂ e) → IsProduct-lowbrow C x y x×y p₁ p₂

    product-as-pullback-to-terminal (make-pullback φ) = make-product χ where

      χ : {a : obj} (f₁ : hom a x) (f₂ : hom a y) → existsUnique (hom a x×y) _≡_ (λ f → (p₁ • f ≡ f₁) × (p₂ • f ≡ f₂))
      χ {a} f₁ f₂ = φ f₁ f₂ (trans (unique-to-1 (t₁ • f₁)) (sym (unique-to-1 (t₂ • f₂))))

  open pullback-to-terminal public

  module terms-pbs-prods {t : obj} (term : IsTerminal C t) (pbs : HasPullbacks C) where

    term↓ = terminal↓ t term
    open IsTerminal-lowbrow term↓

    terminal→pullbacks→products : HasProducts C
    terminal→pullbacks→products x y = record {
      _×_ = _×̣_ ;
      proj₁ = proj₁ ;
      proj₂ = proj₂ ;
      isProduct = product-as-pullback-to-terminal term↓ proj₁ proj₂ t₁ t₂ equation isPullback } where
      t₁ = exists-to-1 x
      t₂ = exists-to-1 y
      open Pullback (pbs t₁ t₂)

  open terms-pbs-prods public

open general-context public