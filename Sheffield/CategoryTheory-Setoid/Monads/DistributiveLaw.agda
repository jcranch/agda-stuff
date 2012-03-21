module Sheffield.CategoryTheory-Setoid.Monads.DistributiveLaw where

open import Level
open import Relation.Binary

open import Sheffield.CategoryTheory-Setoid.Categories
open import Sheffield.CategoryTheory-Setoid.Functors
open import Sheffield.CategoryTheory-Setoid.Functors.Composition
open import Sheffield.CategoryTheory-Setoid.Monads
open import Sheffield.CategoryTheory-Setoid.NaturalTransformations
open import Sheffield.CategoryTheory-Setoid.NaturalTransformations.Equality


record DistributiveLaw {ℓ ℓ′ ℓ″ : Level} {C : Category {ℓ} {ℓ′} {ℓ″}} (M₁ M₂ : Monad C) : Set (ℓ ⊔ ℓ′ ⊔ ℓ″) where

  open Category C
  open Monad M₁ renaming (T to S ; μ to μ₁ ; ε to ε₁ ; unit-l to unit-l₁ ; unit-r to unit-r₁ ; assoc to assoc₁)
  open Monad M₂ renaming (μ to μ₂ ; ε to ε₂ ; unit-l to unit-l₂ ; unit-r to unit-r₂ ; assoc to assoc₂)

  field
    γ : NatTrans (T ⊙ S) (S ⊙ T)

    -- an identity of functors T ⊙ (S ⊙ S) → S ⊙ T
    left-pentagon : ((μ₁ ⊙̂ idNatTrans T)) •̂ ⊙-associator S S T •̂ (idNatTrans S ⊙̂ γ) •̂ ⊙-associator⁻¹ S T S •̂ (γ ⊙̂ idNatTrans S) •̂ ⊙-associator T S S ≈₂ γ •̂ (idNatTrans T ⊙̂ μ₁)

    -- an identity of functors (T ⊙ T) ⊙ S → S ⊙ T
    right-pentagon : (idNatTrans S ⊙̂ μ₂) •̂ ⊙-associator⁻¹ S T T •̂ (γ ⊙̂ idNatTrans T) •̂ ⊙-associator T S T •̂ (idNatTrans T ⊙̂ γ) •̂ ⊙-associator⁻¹ T T S ≈₂ γ •̂ (μ₂ ⊙̂ idNatTrans S)

    -- an identity of functors T → S ⊙ T
    left-triangle : γ •̂ (idNatTrans T ⊙̂ ε₁) •̂ ⊙-unitor-r⁻¹ T ≈₂ (ε₁ ⊙̂ idNatTrans T) •̂ ⊙-unitor-l⁻¹ T

    -- an identity of functors S → S ⊙ T
    right-triangle : γ •̂ (ε₂ ⊙̂ idNatTrans S) •̂ ⊙-unitor-l⁻¹ S ≈₂ (idNatTrans S ⊙̂ ε₂) •̂ ⊙-unitor-r⁻¹ S

  private
    γ₀ = NatTrans.component γ
    e₁ = NatTrans.component ε₁
    e₂ = NatTrans.component ε₂
    u₁ = NatTrans.component μ₁
    u₂ = NatTrans.component μ₂
    S₀ = Functor.obj S
    T₀ = Functor.obj T
    S₁ = λ {x} {y} → Functor.homsets S {x} {y}
    T₁ = λ {x} {y} → Functor.homsets T {x} {y}

  left-pentagon′ : (x : obj) → u₁ (T₀ x) • S₁ (γ₀ x) • γ₀ (S₀ x) ≈ γ₀ x • T₁ (u₁ x)
  left-pentagon′ x = begin
    u₁ (T₀ x) • S₁ (γ₀ x) • γ₀ (S₀ x)
      ≈⟨ •-cong (•-cong (≈-sym (id-r _)) ≈-refl) ≈-refl ⟩
    (u₁ (T₀ x) • id (S₀ (S₀ (T₀ x)))) • S₁ (γ₀ x) • γ₀ (S₀ x)
      ≈⟨ •-cong (•-cong (•-cong ≈-refl (≈-sym (Functor.id S _))) ≈-refl) ≈-refl ⟩
    (u₁ (T₀ x) • S₁ (id (S₀ (T₀ x)))) • S₁ (γ₀ x) • γ₀ (S₀ x)
      ≈⟨ ≈-sym (•-cong (•-cong (•-cong ≈-refl (Functor.hom-cong S (Functor.id S _))) ≈-refl) (id-r _)) ⟩
    (u₁ (T₀ x) • S₁ (S₁ (id (T₀ x)))) • S₁ (γ₀ x) • (γ₀ (S₀ x) • id (T₀ (S₀ (S₀ x))))
      ≈⟨ ≈-sym (•-cong (•-cong (id-r _) (id-l _)) (•-cong ≈-refl (Functor.id T _))) ⟩
    (((u₁ (T₀ x) • S₁ (S₁ (id (T₀ x)))) • id (S₀ (S₀ (T₀ x)))) • (id (S₀ (S₀ (T₀ x))) • S₁ (γ₀ x))) • (γ₀ (S₀ x) • T₁ (id (S₀ (S₀ x))))
      ≈⟨ ≈-sym (•-cong (id-r _) (•-cong ≈-refl (Functor.hom-cong T (Functor.id S _)))) ⟩
    ((((u₁ (T₀ x) • S₁ (S₁ (id (T₀ x)))) • id (S₀ (S₀ (T₀ x)))) • (id (S₀ (S₀ (T₀ x))) • S₁ (γ₀ x))) • (id (S₀ (T₀ (S₀ x))))) • (γ₀ (S₀ x) • T₁ (S₁ (id (S₀ x))))
      ≈⟨ ≈-sym (id-r _) ⟩
    (((((u₁ (T₀ x) • S₁ (S₁ (id (T₀ x)))) • id (S₀ (S₀ (T₀ x)))) • (id (S₀ (S₀ (T₀ x))) • S₁ (γ₀ x))) • (id (S₀ (T₀ (S₀ x))))) • (γ₀ (S₀ x) • T₁ (S₁ (id (S₀ x))))) • (id (T₀ (S₀ (S₀ x))))
      ≈⟨ _≈₂_.component-≈ left-pentagon x ⟩
    γ₀ x • (id (T₀ (S₀ x)) • T₁ (u₁ x))
      ≈⟨ •-cong ≈-refl (id-l _) ⟩
    γ₀ x • T₁ (u₁ x) ∎ where open ≈-Reasoning _ _

  right-pentagon′ : (x : obj) → S₁ (u₂ x) • γ₀ (T₀ x) • T₁ (γ₀ x) ≈ γ₀ x • u₂ (S₀ x)
  right-pentagon′ x = begin
    S₁ (u₂ x) • γ₀ (T₀ x) • T₁ (γ₀ x)
      ≈⟨ •-cong (•-cong ≈-refl (≈-sym (id-r _))) ≈-refl ⟩
    S₁ (u₂ x) • (γ₀ (T₀ x) • id (T₀ (S₀ (T₀ x)))) • T₁ (γ₀ x)
      ≈⟨ •-cong (≈-sym (•-cong (id-l _) (•-cong ≈-refl (Functor.id T _)))) ≈-refl ⟩
    (id (S₀ (T₀ x)) • S₁ (u₂ x)) • (γ₀ (T₀ x) • T₁ (id (S₀ (T₀ x)))) • T₁ (γ₀ x)
      ≈⟨ •-cong (≈-sym (•-cong (id-r _) (•-cong ≈-refl (Functor.hom-cong T (Functor.id S _))))) ≈-refl ⟩
    ((id (S₀ (T₀ x)) • S₁ (u₂ x)) • id (S₀ (T₀ (T₀ x)))) • (γ₀ (T₀ x) • T₁ (S₁ (id (T₀ x)))) • T₁ (γ₀ x)
      ≈⟨ ≈-sym (•-cong (id-r _) (id-l _)) ⟩
    ((((id (S₀ (T₀ x)) • S₁ (u₂ x)) • id (S₀ (T₀ (T₀ x)))) • (γ₀ (T₀ x) • T₁ (S₁ (id (T₀ x))))) • id (T₀ (S₀ (T₀ x)))) • (id (T₀ (S₀ (T₀ x))) • T₁ (γ₀ x))
      ≈⟨ ≈-sym (id-r _) ⟩
    (((((id (S₀ (T₀ x)) • S₁ (u₂ x)) • id (S₀ (T₀ (T₀ x)))) • (γ₀ (T₀ x) • T₁ (S₁ (id (T₀ x))))) • id (T₀ (S₀ (T₀ x)))) • (id (T₀ (S₀ (T₀ x))) • T₁ (γ₀ x))) • id (T₀ (T₀ (S₀ x)))
      ≈⟨ _≈₂_.component-≈ right-pentagon x ⟩
    γ₀ x • (u₂ (S₀ x) • T₁ (T₁ (id (S₀ x))))
      ≈⟨ •-cong ≈-refl (•-cong ≈-refl (Functor.hom-cong T (Functor.id T _))) ⟩
    γ₀ x • (u₂ (S₀ x) • T₁ (id (T₀ (S₀ x))))
      ≈⟨ •-cong ≈-refl (•-cong ≈-refl (Functor.id T _)) ⟩
    γ₀ x • (u₂ (S₀ x) • id (T₀ (T₀ (S₀ x))))
      ≈⟨ •-cong ≈-refl (id-r _) ⟩
    γ₀ x • u₂ (S₀ x) ∎ where open ≈-Reasoning _ _

  left-triangle′ : (x : obj) → γ₀ x • T₁ (e₁ x) ≈ e₁ (T₀ x)
  left-triangle′ x = begin
    γ₀ x • T₁ (e₁ x)
      ≈⟨ •-cong ≈-refl (≈-sym (id-l _)) ⟩
    γ₀ x • (id (T₀ (S₀ x)) • T₁ (e₁ x))
      ≈⟨ •-cong ≈-refl (≈-sym (id-r _)) ⟩
    γ₀ x • ((id (T₀ (S₀ x)) • T₁ (e₁ x)) • id (T₀ x))
      ≈⟨ assoc _ _ _ ⟩
    (γ₀ x • (id (T₀ (S₀ x)) • T₁ (e₁ x))) • id (T₀ x)
      ≈⟨ _≈₂_.component-≈ left-triangle x ⟩
    (e₁ (T₀ x) • id (T₀ x)) • id (T₀ x)
      ≈⟨ id-r _ ⟩
    e₁ (T₀ x) • id (T₀ x)
      ≈⟨ id-r _ ⟩
    e₁ (T₀ x) ∎ where open ≈-Reasoning _ _

  right-triangle′ : (x : obj) → γ₀ x • e₂ (S₀ x) ≈ S₁ (e₂ x)
  right-triangle′ x = begin
    γ₀ x • e₂ (S₀ x)
      ≈⟨ •-cong ≈-refl (≈-sym (id-r _)) ⟩
    γ₀ x • (e₂ (S₀ x) • id (S₀ x))
      ≈⟨ ≈-sym (id-r _) ⟩
    (γ₀ x • (e₂ (S₀ x) • id (S₀ x))) • id (S₀ x)
      ≈⟨ _≈₂_.component-≈ right-triangle x ⟩
    (id (S₀ (T₀ x)) • S₁ (e₂ x)) • id (S₀ x)
      ≈⟨ id-r _ ⟩
    id (S₀ (T₀ x)) • S₁ (e₂ x)
      ≈⟨ id-l _ ⟩
    S₁ (e₂ x) ∎ where open ≈-Reasoning _ _

  composite-unit-l : (x : obj) → _ ≈ _
  composite-unit-l x = begin
    (((((((u₁ (T₀ x) • S₁ (S₁ (u₂ x))) • id (S₀ (S₀ (T₀ (T₀ x))))) • (id (S₀ (S₀ (T₀ (T₀ x)))) • S₁ (id (S₀ (T₀ (T₀ x)))))) • (id (S₀ (S₀ (T₀ (T₀ x)))) • S₁ (γ₀ (T₀ x) • T₁ (S₁ (id (T₀ x)))))) • (id (S₀ (T₀ (S₀ (T₀ x)))) • S₁ (id (T₀ (S₀ (T₀ x)))))) • id (S₀ (T₀ (S₀ (T₀ x))))) • (((e₁ (T₀ (S₀ (T₀ x))) • e₂ (S₀ (T₀ x))) • id (S₀ (T₀ x))) • id (S₀ (T₀ x)))) • id (S₀ (T₀ x))
      ≈⟨ id-r _ ⟩
    ((((((u₁ (T₀ x) • S₁ (S₁ (u₂ x))) • id (S₀ (S₀ (T₀ (T₀ x))))) • (id (S₀ (S₀ (T₀ (T₀ x)))) • S₁ (id (S₀ (T₀ (T₀ x)))))) • (id (S₀ (S₀ (T₀ (T₀ x)))) • S₁ (γ₀ (T₀ x) • T₁ (S₁ (id (T₀ x)))))) • (id (S₀ (T₀ (S₀ (T₀ x)))) • S₁ (id (T₀ (S₀ (T₀ x)))))) • id (S₀ (T₀ (S₀ (T₀ x))))) • (((e₁ (T₀ (S₀ (T₀ x))) • e₂ (S₀ (T₀ x))) • id (S₀ (T₀ x))) • id (S₀ (T₀ x)))
      ≈⟨ •-cong (id-r _) (id-r _) ⟩
    (((((u₁ (T₀ x) • S₁ (S₁ (u₂ x))) • id (S₀ (S₀ (T₀ (T₀ x))))) • (id (S₀ (S₀ (T₀ (T₀ x)))) • S₁ (id (S₀ (T₀ (T₀ x)))))) • (id (S₀ (S₀ (T₀ (T₀ x)))) • S₁ (γ₀ (T₀ x) • T₁ (S₁ (id (T₀ x)))))) • (id (S₀ (T₀ (S₀ (T₀ x)))) • S₁ (id (T₀ (S₀ (T₀ x)))))) • ((e₁ (T₀ (S₀ (T₀ x))) • e₂ (S₀ (T₀ x))) • id (S₀ (T₀ x)))
      ≈⟨ •-cong (•-cong (•-cong (•-cong (id-r _) (id-l _)) (id-l _)) (id-l _)) (id-r _) ⟩
    ((((u₁ (T₀ x) • S₁ (S₁ (u₂ x))) • S₁ (id (S₀ (T₀ (T₀ x))))) • S₁ (γ₀ (T₀ x) • T₁ (S₁ (id (T₀ x))))) • S₁ (id (T₀ (S₀ (T₀ x))))) • (e₁ (T₀ (S₀ (T₀ x))) • e₂ (S₀ (T₀ x)))
      ≈⟨ •-cong (•-cong (•-cong (•-cong ≈-refl (Functor.id S _)) ≈-refl) (Functor.id S _)) ≈-refl ⟩
    (((u₁ (T₀ x) • S₁ (S₁ (u₂ x))) • id (S₀ (S₀ (T₀ (T₀ x))))) • S₁ (γ₀ (T₀ x) • T₁ (S₁ (id (T₀ x)))) • id (S₀ (T₀ (S₀ (T₀ x))))) • (e₁ (T₀ (S₀ (T₀ x))) • e₂ (S₀ (T₀ x)))
      ≈⟨ •-cong (id-r _) ≈-refl ⟩
    ((u₁ (T₀ x) • S₁ (S₁ (u₂ x))) • id (S₀ (S₀ (T₀ (T₀ x))))) • S₁ (γ₀ (T₀ x) • T₁ (S₁ (id (T₀ x)))) • (e₁ (T₀ (S₀ (T₀ x))) • e₂ (S₀ (T₀ x)))
      ≈⟨ •-cong (•-cong (id-r _) (Functor.hom-cong S (•-cong ≈-refl (Functor.hom-cong T (Functor.id S _))))) ≈-refl ⟩
    (u₁ (T₀ x) • S₁ (S₁ (u₂ x))) • S₁ (γ₀ (T₀ x) • T₁ (id (S₀ (T₀ x)))) • (e₁ (T₀ (S₀ (T₀ x))) • e₂ (S₀ (T₀ x)))
      ≈⟨ •-cong (•-cong ≈-refl (Functor.hom-cong S (•-cong ≈-refl (Functor.id T _)))) ≈-refl ⟩
    (u₁ (T₀ x) • S₁ (S₁ (u₂ x))) • S₁ (γ₀ (T₀ x) • id (T₀ (S₀ (T₀ x)))) • (e₁ (T₀ (S₀ (T₀ x))) • e₂ (S₀ (T₀ x)))
      ≈⟨ •-cong (•-cong ≈-refl (Functor.hom-cong S (id-r _))) ≈-refl ⟩
    (u₁ (T₀ x) • S₁ (S₁ (u₂ x))) • S₁ (γ₀ (T₀ x)) • (e₁ (T₀ (S₀ (T₀ x))) • e₂ (S₀ (T₀ x)))
      ≈⟨ {!!} ⟩
    id (S₀ (T₀ x)) ∎ where open ≈-Reasoning _ _

  composite : Monad C
  composite = record {
    T = S ⊙ T ;
    μ = (μ₁ ⊙̂ μ₂) •̂ ⊙-associator S S (T ⊙ T) •̂ (idNatTrans S ⊙̂ ⊙-associator⁻¹ S T T) •̂ (idNatTrans S ⊙̂ (γ ⊙̂ idNatTrans T)) •̂ (idNatTrans S ⊙̂ ⊙-associator T S T) •̂ ⊙-associator⁻¹ S T (S ⊙ T) ; 
    ε = (ε₁ ⊙̂ ε₂) •̂ ⊙-unitor-l⁻¹ (idFunctor C) ; 
    unit-l = make-≈₂ composite-unit-l ;
    unit-r = make-≈₂ {!!} ;
    assoc = make-≈₂ {!!} }


{-
(((((((u₁ (T₀ x) • S₁ (S₁ (u₂ x))) • id (S₀ (S₀ (T₀ (T₀ x))))) • (id (S₀ (S₀ (T₀ (T₀ x)))) • S₁ (id (S₀ (T₀ (T₀ x)))))) • (id (S₀ (S₀ (T₀ (T₀ x)))) • S₁ (γ₀ (T₀ x) • T₁ (S₁ (id (T₀ x)))))) • (id (S₀ (T₀ (S₀ (T₀ x)))) • S₁ (id (T₀ (S₀ (T₀ x)))))) • id (S₀ (T₀ (S₀ (T₀ x))))) • (((e₁ (T₀ (S₀ (T₀ x))) • e₂ (S₀ (T₀ x))) • id (S₀ (T₀ x))) • id (S₀ (T₀ x)))) • id (S₀ (T₀ x))

id (S₀ (T₀ x))
-}


-- these other two laws have us equating...
-- (needs _•_ notation)



{-
 ((compose ((compose ((compose ((compose ((compose ((compose ((compose ((compose (u₁ (T₀ x))) (S₁ (S₁ (u₂ x))))) (id (S₀ (S₀ (T₀ (T₀ x))))))) ((compose (id (S₀ (S₀ (T₀ (T₀ x)))))) (S₁ (id (S₀ (T₀ (T₀ x)))))))) ((compose (id (S₀ (S₀ (T₀ (T₀ x)))))) (S₁ ((compose (γ₀ (T₀ x))) (T₁ (S₁ (id (T₀ x))))))))) ((compose (id (S₀ (T₀ (S₀ (T₀ x)))))) (S₁ (id (T₀ (S₀ (T₀ x)))))))) (id (S₀ (T₀ (S₀ (T₀ x))))))) ((compose (id (S₀ (T₀ (S₀ (T₀ x)))))) (S₁ (T₁ ((compose ((compose (e₁ (T₀ x))) (e₂ x))) (id x))))))) (id (S₀ (T₀ x))))

id (S₀ (T₀ x))
-}


{-
((compose ((compose ((compose ((compose ((compose ((compose ((compose ((compose (u₁ (T₀ x))) (S₁ (S₁ (u₂ x))))) (id (S₀ (S₀ (T₀ (T₀ x))))))) ((compose (id (S₀ (S₀ (T₀ (T₀ x)))))) (S₁ (id (S₀ (T₀ (T₀ x)))))))) ((compose (id (S₀ (S₀ (T₀ (T₀ x)))))) (S₁ ((compose (γ₀ (T₀ x))) (T₁ (S₁ (id (T₀ x))))))))) ((compose (id (S₀ (T₀ (S₀ (T₀ x)))))) (S₁ (id (T₀ (S₀ (T₀ x)))))))) (id (S₀ (T₀ (S₀ (T₀ x))))))) ((compose (id (S₀ (T₀ (S₀ (T₀ x)))))) (S₁ (T₁ ((compose ((compose ((compose ((compose ((compose ((compose (u₁ (T₀ x))) (S₁ (S₁ (u₂ x))))) (id (S₀ (S₀ (T₀ (T₀ x))))))) ((compose (id (S₀ (S₀ (T₀ (T₀ x)))))) (S₁ (id (S₀ (T₀ (T₀ x)))))))) ((compose (id (S₀ (S₀ (T₀ (T₀ x)))))) (S₁ ((compose (γ₀ (T₀ x))) (T₁ (S₁ (id (T₀ x))))))))) ((compose (id (S₀ (T₀ (S₀ (T₀ x)))))) (S₁ (id (T₀ (S₀ (T₀ x)))))))) (id (S₀ (T₀ (S₀ (T₀ x))))))))))) (id (S₀ (T₀ (S₀ (T₀ (S₀ (T₀ x))))))))

((compose ((compose ((compose ((compose ((compose ((compose ((compose (u₁ (T₀ x))) (S₁ (S₁ (u₂ x))))) (id (S₀ (S₀ (T₀ (T₀ x))))))) ((compose (id (S₀ (S₀ (T₀ (T₀ x)))))) (S₁ (id (S₀ (T₀ (T₀ x)))))))) ((compose (id (S₀ (S₀ (T₀ (T₀ x)))))) (S₁ ((compose (γ₀ (T₀ x))) (T₁ (S₁ (id (T₀ x))))))))) ((compose (id (S₀ (T₀ (S₀ (T₀ x)))))) (S₁ (id (T₀ (S₀ (T₀ x)))))))) (id (S₀ (T₀ (S₀ (T₀ x))))))) ((compose ((compose ((compose ((compose ((compose ((compose ((compose (u₁ (T₀ (S₀ (T₀ x))))) (S₁ (S₁ (u₂ (S₀ (T₀ x))))))) (id (S₀ (S₀ (T₀ (T₀ (S₀ (T₀ x))))))))) ((compose (id (S₀ (S₀ (T₀ (T₀ (S₀ (T₀ x)))))))) (S₁ (id (S₀ (T₀ (T₀ (S₀ (T₀ x)))))))))) ((compose (id (S₀ (S₀ (T₀ (T₀ (S₀ (T₀ x)))))))) (S₁ ((compose (γ₀ (T₀ (S₀ (T₀ x))))) (T₁ (S₁ (id (T₀ (S₀ (T₀ x))))))))))) ((compose (id (S₀ (T₀ (S₀ (T₀ (S₀ (T₀ x)))))))) (S₁ (id (T₀ (S₀ (T₀ (S₀ (T₀ x)))))))))) (id (S₀ (T₀ (S₀ (T₀ (S₀ (T₀ x))))))))) (S₁ (T₁ (S₁ (T₁ (id (S₀ (T₀ x)))))))))
-}