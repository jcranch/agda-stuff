module Sheffield.CategoryTheory-Setoid.NaturalTransformations.Equality where


open import Function.Equality
open import Level
open import Relation.Binary
import Relation.Binary.EqReasoning

open import Sheffield.CategoryTheory-Setoid.Categories
open import Sheffield.CategoryTheory-Setoid.Functors
open import Sheffield.CategoryTheory-Setoid.NaturalTransformations



module natural-transformation-equalities {ℓ₁ ℓ′₁ ℓ″₁ ℓ₂ ℓ′₂ ℓ″₂ : Level}
       {C : Category {ℓ₁} {ℓ′₁} {ℓ″₁}} {D : Category {ℓ₂} {ℓ′₂} {ℓ″₂}} {F G : Functor C D} where

  open Category D

  infix 4 _≈₂_
  record _≈₂_ (Φ : NatTrans F G) (Ψ : NatTrans F G) : Set (ℓ₁ ⊔ ℓ″₂) where
    constructor make-≈₂
    field
      component-≈ : (x : Category.obj C) → NatTrans.component Φ x ≈ NatTrans.component Ψ x


  ≈₂-refl : {Θ : NatTrans F G} → Θ ≈₂ Θ
  ≈₂-refl = make-≈₂ (λ x → ≈-refl)


  ≈₂-sym : {Φ Ψ : NatTrans F G} → Φ ≈₂ Ψ → Ψ ≈₂ Φ
  ≈₂-sym (make-≈₂ component-≈) = make-≈₂ (λ x → ≈-sym (component-≈ x))


  ≈₂-trans : {Θ Φ Ψ : NatTrans F G} →
           Θ ≈₂ Φ → Φ ≈₂ Ψ → Θ ≈₂ Ψ
  ≈₂-trans (make-≈₂ component-≈) (make-≈₂ component′-≈) = make-≈₂ (λ x → ≈-trans (component-≈ x) (component′-≈ x))


  ≈₂-isEquivalence :  IsEquivalence _≈₂_
  ≈₂-isEquivalence = record {
    refl  = λ {Θ : NatTrans F G} → ≈₂-refl {Θ = Θ} ;
    sym   = λ {Φ Ψ : NatTrans F G} e → ≈₂-sym {Φ = Φ} {Ψ = Ψ} e ; 
    trans = λ {Θ Φ Ψ : NatTrans F G} e₁ e₂ → ≈₂-trans {Θ = Θ} {Φ = Φ} {Ψ = Ψ} e₁ e₂ }


  NaturalTransformations : Setoid (ℓ₁ ⊔ ℓ′₁ ⊔ ℓ″₁ ⊔ ℓ₂ ⊔ ℓ′₂ ⊔ ℓ″₂) (ℓ₁ ⊔ ℓ″₂)
  NaturalTransformations = record {
    Carrier       = NatTrans F G ;
    _≈_           = _≈₂_ ;
    isEquivalence = ≈₂-isEquivalence }

  module NatTrans-reasoning = Relation.Binary.EqReasoning NaturalTransformations

open natural-transformation-equalities public
