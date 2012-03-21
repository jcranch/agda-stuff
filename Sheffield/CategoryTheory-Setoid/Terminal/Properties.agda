module Sheffield.CategoryTheory-Setoid.Terminal.Properties where

open import Function.Equality hiding (id)
open import Level
open import Relation.Binary

open import Sheffield.CategoryTheory-Setoid.Categories
open import Sheffield.CategoryTheory-Setoid.Categories.Equivalence
open import Sheffield.CategoryTheory-Setoid.Categories.Equivalence.Properties
open import Sheffield.CategoryTheory-Setoid.Comma
open import Sheffield.CategoryTheory-Setoid.Functors
open import Sheffield.CategoryTheory-Setoid.Functors.Isomorphism
open import Sheffield.CategoryTheory-Setoid.Functors.Isomorphism.Properties
open import Sheffield.CategoryTheory-Setoid.Terminal
open import Sheffield.CategoryTheory-Setoid.NaturalTransformations
open import Sheffield.CategoryTheory-Setoid.NaturalTransformations.Equality



module terminal-isos {ℓ₁ ℓ′₁ ℓ″₁ : Level} {C : Category {ℓ₁} {ℓ′₁} {ℓ″₁}} where

  open Category C
  open Iso C

  -- if you're isomorphic to a terminal object, you're a terminal object
  terminal-stable : (t₁ t₂ : obj) → t₁ ≅ t₂ → IsTerminal C t₁ → IsTerminal C t₂
  terminal-stable t₁ t₂ (Iso.make-≅ f (Iso.makeIso f⁻¹ unit counit)) (make-terminal exists unique) = make-terminal exists′ unique′ where
    exists′ : (x : obj) → homset x t₂
    exists′ x = f • exists x
    unique′ : {x : obj} (g : homset x t₂) → g ≈ exists′ x
    unique′ {x} g = begin
      g
        ≈⟨ ≈-sym (id-l _) ⟩
      id _ • g
        ≈⟨ •-cong (≈-sym counit) ≈-refl ⟩
      (f • f⁻¹) • g
        ≈⟨ assoc _ _ _ ⟩
      f • (f⁻¹ • g)
        ≈⟨ •-cong ≈-refl (unique _) ⟩
      f • exists x ∎ where open ≈-Reasoning x t₂

open terminal-isos public



-- terminal objects are preserved by equivalences
terminal-preservation : {ℓ₁ ℓ′₁ ℓ″₁ ℓ₂ ℓ′₂ ℓ″₂ : Level}
  {C : Category {ℓ₁} {ℓ′₁} {ℓ″₁}}  {D : Category {ℓ₂} {ℓ′₂} {ℓ″₂}}
  (F : Functor C D) (F̃ : Equivalence₀ F)
  (t : Category.obj C) (term : IsTerminal C t) → IsTerminal D (Functor.obj F t)
terminal-preservation {C = C} {D = D} F (make-Equiv₀ G unit counit) t (make-terminal exists unique) = record {
  exists = exists′ ;
  unique = unique′  } where
  open Category D
  open Category C using () renaming (_≈_ to _≈′_)
  open Iso C
  F₀ = Functor.obj F
  G₀ = Functor.obj G
  G₁ = λ {x} {y} f → Functor.homsets G {x} {y} f
  exists′ : (x : obj) → _
  exists′ y = Functor.homsets F (exists (Functor.obj G y)) • NatTrans.component (_≅₁_.reverse counit) y
  unique′ : {x : obj} (f : homset x (F₀ t)) → _ ≈ _
  unique′ {x} f = equivalence-faithful G (make-Equiv₀ F counit unit) x (F₀ t) e where
    t≅GFt : t ≅ G₀ (F₀ t)
    t≅GFt = make-iso (NatTrans.component (_≅₁_.reverse unit) t) (NatTrans.component (_≅₁_.obverse unit) t) (_≈₂_.component-≈ (_≅₁_.counit unit) t) (_≈₂_.component-≈ (_≅₁_.unit unit) t)
    term′ : IsTerminal C (G₀ (F₀ t))
    term′ = terminal-stable t (G₀ (F₀ t)) t≅GFt (make-terminal exists unique)
    e : G₁ f ≈′ G₁ (exists′ x)
    e = IsTerminal.any-two-equal C term′ (G₁ f) (G₁ (exists′ x))
