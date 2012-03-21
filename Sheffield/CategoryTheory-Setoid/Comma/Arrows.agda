module Sheffield.CategoryTheory-Setoid.Comma.Arrows where

open import Data.Fin
open import Data.Nat using (z≤n ; s≤s)
open import Data.Product
open import Data.Unit hiding (_≤_ ; unit)
open import Function.Equality hiding (id)
open import Level

open import Sheffield.CategoryTheory-Setoid.Categories
open import Sheffield.CategoryTheory-Setoid.Categories.Equivalence
open import Sheffield.CategoryTheory-Setoid.Categories.Equivalence.Properties
open import Sheffield.CategoryTheory-Setoid.Comma
open import Sheffield.CategoryTheory-Setoid.Examples.Simplex
open import Sheffield.CategoryTheory-Setoid.Functors
open import Sheffield.CategoryTheory-Setoid.Functors.Category
open import Sheffield.CategoryTheory-Setoid.Functors.Isomorphism
open import Sheffield.CategoryTheory-Setoid.NaturalTransformations
open import Sheffield.CategoryTheory-Setoid.NaturalTransformations.Equality
open arrow-category



arrows-agreement : {ℓ ℓ′ ℓ″ : Level} (C : Category {ℓ} {ℓ′} {ℓ″}) → Functors arrow C ≅₀ Comma (idFunctor C) (idFunctor C)
arrows-agreement C = make-≅₀ R (assemble-equivalence R R-faithful R-full R-ess-surj) where

  open Category C
  open comma-category.comma-structure (idFunctor C) (idFunctor C) hiding (id-l ; id-r ; assoc)

  fun2 : {ℓ₁ : Level} {A : Fin 2 → Set ℓ₁} → A (Fin.zero) → A (Fin.suc Fin.zero) → (i : Fin 2) → A i
  fun2 x y Fin.zero = x
  fun2 x y (Fin.suc Fin.zero) = y
  fun2 x y (Fin.suc (Fin.suc ()))


  R : Functor (Functors arrow C) (Comma (idFunctor C) (idFunctor C))
  R = makeFunctor R₀ R₁ R-id R-compose where

    R₀ : Functor arrow C → Comma-obj
    R₀ F = [ Functor.obj F s , Functor.obj F t , Functor.homsets F s→t ]

    R₁ : {F G : Functor arrow C} → NaturalTransformations {F = F} {G = G} ⟶ Comma-hom (R₀ F) (R₀ G)
    R₁ {F} {G} = record {
      _⟨$⟩_ = λ Θ → make-hom (NatTrans.component Θ s) (NatTrans.component Θ t) (NatTrans.naturality Θ s→t);
      cong = λ e → _≈₂_.component-≈ e s ,′ _≈₂_.component-≈ e t }

    R-id : (F : Functor arrow C) → _
    R-id F = ≈-refl ,′ ≈-refl

    R-compose : {F G H : Functor arrow C} (Θ : NatTrans G H) (Φ : NatTrans F G) → _
    R-compose Θ Φ = ≈-refl ,′ ≈-refl

  R-faithful : faithful R
  R-faithful F G e = make-≈₂ (fun2 (proj₁ e) (proj₂ e))

  R-full : full R
  R-full F G = record {
    from = record {
      _⟨$⟩_ = λ f → makeNatTrans (fun2 (Comma-homset.mor₁ f) (Comma-homset.mor₂ f)) {!!} ;
      cong = λ {f₁} {f₂} ε → make-≈₂ (fun2 (proj₁ ε) (proj₂ ε)) };
    right-inverse-of = λ f → ≈-refl ,′ ≈-refl } 

  R-ess-surj : essentially-surjective R
  R-ess-surj = record {
    from = record {
      _⟨$⟩_ = λ F → makeFunctor (fun2 (Comma-obj.s F) (Comma-obj.t F)) {!!} {!!} {!!};
      cong = λ {F₁} {F₂} ε → {!!} };
    right-inverse-of = λ F → {!!} }

