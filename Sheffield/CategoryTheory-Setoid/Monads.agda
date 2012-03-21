module Sheffield.CategoryTheory-Setoid.Monads where

open import Function.Equality hiding (id ; _⟶_) renaming (_⇨_ to _⟶_)
open import Level
open import Relation.Binary

open import Sheffield.CategoryTheory-Setoid.Categories
open import Sheffield.CategoryTheory-Setoid.Functors
open import Sheffield.CategoryTheory-Setoid.Functors.Composition
open import Sheffield.CategoryTheory-Setoid.NaturalTransformations
open import Sheffield.CategoryTheory-Setoid.NaturalTransformations.Equality
open import Sheffield.CategoryTheory-Setoid.SetoidFunction



record Monad {ℓ ℓ′ ℓ″ : Level} (C : Category {ℓ} {ℓ′} {ℓ″}) : Set (ℓ ⊔ ℓ′ ⊔ ℓ″) where

  constructor makeMonad

  field
    T : Functor C C
    μ : NatTrans (T ⊙ T) T
    ε : NatTrans (idFunctor C) T

    unit-l : μ •̂ (ε ⊙̂ idNatTrans T) •̂ ⊙-unitor-l⁻¹ T ≈₂ idNatTrans T
    unit-r : μ •̂ (idNatTrans T ⊙̂ ε) •̂ ⊙-unitor-r⁻¹ T ≈₂ idNatTrans T
    assoc : μ •̂ (idNatTrans T ⊙̂ μ) •̂ ⊙-associator⁻¹ T T T ≈₂ μ •̂ (μ ⊙̂ idNatTrans T)



module monad-constructions {ℓ ℓ′ ℓ″ : Level} {C : Category {ℓ} {ℓ′} {ℓ″}} (M : Monad C) where

  open Category C
  open Monad M renaming (assoc to assoc′)

  record Algebra : Set (ℓ ⊔ ℓ′) where
    constructor makeAlgebra
    field
      carrier : obj
      structure : homset (Functor.obj T carrier) carrier

  record algebra-homset (A B : Algebra) : Set (ℓ ⊔ ℓ′ ⊔ ℓ″) where
    constructor make-algebra-hom

    open Algebra A renaming (carrier to X ; structure to f)
    open Algebra B renaming (carrier to Y ; structure to g)

    field
      carrier-hom : homset X Y
      structure-eq : g • Functor.homsets T carrier-hom ≈ carrier-hom • f

  algebra-hom-≈ : {A B : Algebra} → Rel (algebra-homset A B) ℓ″
  algebra-hom-≈ F G = algebra-homset.carrier-hom F ≈ algebra-homset.carrier-hom G

  algebra-hom : (A B : Algebra) → Setoid (ℓ ⊔ ℓ′ ⊔ ℓ″) ℓ″
  algebra-hom A B = record {
    Carrier = algebra-homset A B;
    _≈_ = algebra-hom-≈;
    isEquivalence = record {
      refl = ≈-refl;
      sym = ≈-sym;
      trans = ≈-trans } }

  private

    alg-id : (A : Algebra) → algebra-homset A A
    alg-id (makeAlgebra carrier structure) = record {
      carrier-hom = id carrier ;
      structure-eq = ≈-trans (≈-trans (•-cong ≈-refl (Functor.id T carrier)) (id-r _)) (≈-sym (id-l _)) }

    alg-• : {A B C : Algebra} → algebra-homset B C → algebra-homset A B → algebra-homset A C
    alg-• {makeAlgebra _ p} {makeAlgebra _ q} {makeAlgebra _ r} (make-algebra-hom g e′) (make-algebra-hom f e) = make-algebra-hom (g • f) e″ where
      open ≈-Reasoning _ _
      e″ = begin
        r • Functor.homsets T (g • f)
          ≈⟨ •-cong ≈-refl (Functor.compose T _ _) ⟩
        r • (Functor.homsets T g • Functor.homsets T f)
          ≈⟨ ≈-sym (assoc _ _ _) ⟩
        (r • Functor.homsets T g) • Functor.homsets T f
          ≈⟨ •-cong e′ ≈-refl ⟩
        (g • q) • Functor.homsets T f
          ≈⟨ assoc _ _ _ ⟩
        g • (q • Functor.homsets T f)
          ≈⟨ •-cong ≈-refl e ⟩
        g • (f • p)
          ≈⟨ ≈-sym (assoc _ _ _) ⟩
        (g • f) • p ∎

    alg-compose : {A B C : Algebra} → Γ (algebra-hom B C ⟶ algebra-hom A B ⟶ algebra-hom A C)
    alg-compose = record {
      _⟨$⟩_ = λ G → record {
        _⟨$⟩_ = alg-• G;
        cong = λ e → •-cong ≈-refl e };
      cong = λ e₁ e₂ → •-cong e₁ e₂ }

  algebras : Category {ℓ ⊔ ℓ′} {ℓ ⊔ ℓ′ ⊔ ℓ″} {ℓ″}
  algebras = record {
    obj = Algebra ;
    hom = algebra-hom ;
    id = alg-id ;
    compose = alg-compose ;
    id-l = λ f → id-l (algebra-homset.carrier-hom f) ;
    id-r = λ f → id-r (algebra-homset.carrier-hom f) ;
    assoc = λ h g f → assoc (algebra-homset.carrier-hom h) (algebra-homset.carrier-hom g) (algebra-homset.carrier-hom f) }

open monad-constructions public