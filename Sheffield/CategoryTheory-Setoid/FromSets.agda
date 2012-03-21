module Sheffield.CategoryTheory-Setoid.FromSets where

open import Level
open import Relation.Binary
open import Relation.Binary.PropositionalEquality


open import Sheffield.CategoryTheory-Set.Categories using (makeCat) renaming (Category to Category⁻)
open import Sheffield.CategoryTheory-Setoid.Categories using () renaming (Category to Category⁺)

open import Sheffield.CategoryTheory-Set.Functors using (makeFunctor) renaming (Functor to Functor⁻)
open import Sheffield.CategoryTheory-Setoid.Functors using () renaming (Functor to Functor⁺)

open import Sheffield.CategoryTheory-Set.NaturalTransformations using (makeNatTrans) renaming (NatTrans to NatTrans⁻)
open import Sheffield.CategoryTheory-Setoid.NaturalTransformations using () renaming (NatTrans to NatTrans⁺)


category-fromSet : {ℓ ℓ′ : Level} → Category⁻ {ℓ} {ℓ′} → Category⁺ {ℓ} {ℓ′} {ℓ′}
category-fromSet (makeCat obj hom id compose id-l id-r assoc) = record {
  obj = obj ;
  hom = λ x y → setoid (hom x y) ;
  id = id ;
  compose = record {
    _⟨$⟩_ = λ g → record {
      _⟨$⟩_ = compose g ;
      cong = cong (compose g) } ;
    cong = λ e₁ e₂ → cong₂ compose e₁ e₂ } ;
  id-l = id-l ;
  id-r = id-r ;
  assoc = λ h g f → sym (assoc h g f) }

functor-fromSet : {ℓ₁ ℓ′₁ ℓ₂ ℓ′₂ : Level} {C : Category⁻ {ℓ₁} {ℓ′₁}} {D : Category⁻ {ℓ₂} {ℓ′₂}} → Functor⁻ C D → Functor⁺ (category-fromSet C) (category-fromSet D)
functor-fromSet (makeFunctor obj hom id compose) = record {
  obj = obj ;
  hom = record {
    _⟨$⟩_ = hom ;
    cong = cong hom } ;
  id = id ;
  compose = compose }

nattrans-fromSet : {ℓ₁ ℓ′₁ ℓ₂ ℓ′₂ : Level} {C : Category⁻ {ℓ₁} {ℓ′₁}} {D : Category⁻ {ℓ₂} {ℓ′₂}} {F G : Functor⁻ C D} → NatTrans⁻ F G → NatTrans⁺ (functor-fromSet F) (functor-fromSet G)
nattrans-fromSet (makeNatTrans component naturality) = record {
  component = component ;
  naturality = naturality }
