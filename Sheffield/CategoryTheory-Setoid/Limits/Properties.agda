module Sheffield.CategoryTheory-Setoid.Limits.Properties where

open import Data.Unit using (tt)
open import Level
open import Relation.Binary

open import Sheffield.CategoryTheory-Setoid.Categories
open import Sheffield.CategoryTheory-Setoid.Categories.Diagrams
open import Sheffield.CategoryTheory-Setoid.Comma using (module comma-category)
open import Sheffield.CategoryTheory-Setoid.Functors
open import Sheffield.CategoryTheory-Setoid.Functors.Category
open import Sheffield.CategoryTheory-Setoid.Limits
open import Sheffield.CategoryTheory-Setoid.Terminal
open import Sheffield.CategoryTheory-Setoid.NaturalTransformations
open import Sheffield.CategoryTheory-Setoid.NaturalTransformations.Equality



module induced-maps-context {ℓ₁ ℓ′₁ ℓ″₁ ℓ₂ ℓ′₂ ℓ″₂ : Level}
  {K : Category {ℓ₁} {ℓ′₁} {ℓ″₁}} {C : Category {ℓ₂} {ℓ′₂} {ℓ″₂}} where

  open Category C

  module induced-maps {F₁ F₂ : Functor K C} (lim₁ : Limit F₁) (lim₂ : Limit F₂) where

    open comma-category (constFunctors K C) (constFunctor point (Functors K C) F₂)
    open comma-structure

    induced-map : (Θ : NatTrans F₁ F₂) → Category.homset C (Limit.object lim₁) (Limit.object lim₂)
    induced-map Θ = Functor.homsets Proj₁ f where
      c₁ : Category.obj Comma
      c₁ = [ Limit.object lim₁ , tt , Θ •̂ Limit.cone-trans lim₁ ]
      c₂ : Category.obj Comma
      c₂ = Limit.cone lim₂
      f : Category.homset Comma c₁ c₂
      f = IsTerminal.exists Comma (Limit.limiting lim₂) c₁

    induced-map-≈ : (Θ Φ : NatTrans F₁ F₂) → Θ ≈₂ Φ → induced-map Θ ≈ induced-map Φ
    induced-map-≈ Θ Φ e = {!!}

  open induced-maps public

  induced-map-id : (F : Functor K C) (lim : Limit F) → induced-map lim lim (idNatTrans F) ≈ id (Limit.object lim)
  induced-map-id F lim = {!!}

  induced-map-compose : {F₁ F₂ F₃ : Functor K C} (lim₁ : Limit F₁) (lim₂ : Limit F₂) (lim₃ : Limit F₃) (Ψ : NatTrans F₂ F₃) (Θ : NatTrans F₁ F₂) → induced-map lim₂ lim₃ Ψ • induced-map lim₁ lim₂ Θ ≈ induced-map lim₁ lim₃ (Ψ •̂ Θ)
  induced-map-compose lim₁ lim₂ lim₃ Ψ Θ = {!!}
  


  module limit-functoriality {ℓ ℓ′ ℓ″ : Level} {A : Category {ℓ} {ℓ′} {ℓ″}}
    (F : Functor A (Functors K C))
    (lim : (a : Category.obj A) → Limit (Functor.obj F a)) where

    -- more general statements are possible: we could construct a
    -- functor into Functors from the cone category on K to C
    functoriality : Functor A C
    functoriality = record {
      obj = λ x → Limit.object (lim x) ;
      hom = λ {x} {y} → record {
        _⟨$⟩_ = λ f → induced-map (lim x) (lim y) (Functor.homsets F f) ;
        cong = λ {f} {g} e → induced-map-≈ (lim x) (lim y) (Functor.homsets F f) (Functor.homsets F g) (Functor.hom-cong F e) } ;
      id = λ x → {!!} ; -- induced-map-id (Functor.obj F x) {!lim x!} ;
      compose = λ {x} {y} {z} g f → {!induced-map-compose (lim x) (lim y) (lim z) (Functor.homsets F g) (Functor.homsets F f)!} }

  open limit-functoriality public

open induced-maps-context public