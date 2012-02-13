module Limits.Properties where

open import Level

open import Categories
open import Functors
open import Limits
open import Misc
open import NaturalTransformations


hom-between-limits : {ℓ₁ ℓ′₁ ℓ₂ ℓ′₂ : Level}
  {K : Category {ℓ₁} {ℓ′₁}} {C : Category {ℓ₂} {ℓ′₂}}
  (F G : Functor K C) (x y : Category.obj C)
  (Φ : NatTrans (constFunctor K C x) F) →
  (Ψ : NatTrans (constFunctor K C y) G) →
  IsLimit G y Ψ → NatTrans F G → Category.hom C x y

hom-between-limits F G x y Φ Ψ lim Θ = existsUnique.witness (IsLimit.factorisations lim x (Θ •̂ Φ))