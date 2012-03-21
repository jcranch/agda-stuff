module Sheffield.CategoryTheory-Setoid.Examples.Categories where

open import Level
open import Relation.Binary

open import Sheffield.CategoryTheory-Setoid.Categories
open import Sheffield.CategoryTheory-Setoid.Functors
open import Sheffield.CategoryTheory-Setoid.Functors.Category
open import Sheffield.CategoryTheory-Setoid.Functors.CompositionEqualities
open import Sheffield.CategoryTheory-Setoid.Functors.Isomorphism
open import Sheffield.CategoryTheory-Setoid.Functors.Isomorphism.Properties


Categories : {ℓ ℓ′ ℓ″ : Level} → Category {suc (ℓ ⊔ ℓ′ ⊔ ℓ″)} {ℓ ⊔ ℓ′ ⊔ ℓ″} {ℓ ⊔ ℓ′ ⊔ ℓ″}
Categories {ℓ} {ℓ′} {ℓ″} = record {
  obj = Category {ℓ} {ℓ′} {ℓ″} ;
  hom = functors ;
  id = idFunctor ;
  compose = record {
    _⟨$⟩_ = λ G → record {
      _⟨$⟩_ = _⊙_ G;
      cong = λ eF → ≅₁-cong (≅₁-refl G) eF } ;
    cong = λ eG eF → ≅₁-cong eG eF } ;
  id-l = ⊙-unital-l ;
  id-r = ⊙-unital-r ;
  assoc = ⊙-associative }
