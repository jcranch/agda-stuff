module Sheffield.CategoryTheory-Setoid.Comma.Opposites where

open import Algebra.Structures
open import Data.Product
open import Function using (flip ; _∘_)
open import Function.Equality hiding (id ; _∘_)
open import Level
open import Relation.Binary

open import Sheffield.CategoryTheory-Setoid.Categories
open import Sheffield.CategoryTheory-Setoid.Categories.Equivalence
open import Sheffield.CategoryTheory-Setoid.Comma
open import Sheffield.CategoryTheory-Setoid.Functors
open import Sheffield.CategoryTheory-Setoid.Functors.Isomorphism
open import Sheffield.CategoryTheory-Setoid.NaturalTransformations
open import Sheffield.CategoryTheory-Setoid.NaturalTransformations.Equality
open import Sheffield.CategoryTheory-Setoid.SetoidFunction



-- these categories are much closer than merely equivalent; they're isomorphic in a
-- very canonical way. But I haven't found a shortcut: isomorphisms of categories
-- are deeply unpleasant.

comma-opposite : {ℓ₁ ℓ′₁ ℓ″₁ ℓ₂ ℓ′₂ ℓ″₂ ℓ₃ ℓ′₃ ℓ″₃ : Level} {A : Category {ℓ₁} {ℓ′₁} {ℓ″₁}} {B : Category {ℓ₂} {ℓ′₂} {ℓ″₂}} {C : Category {ℓ₃} {ℓ′₃} {ℓ″₃}} (F : Functor A C) (G : Functor B C) → opposite (Comma F G) ≅₀ Comma (functor-op G) (functor-op F)
comma-opposite {A = A} {B = B} {C = C} F G = equivalent₀ obv rev unit counit where
  open Category C using (≈-sym)

  open comma-category.comma-structure F G
  open comma-category.comma-structure (functor-op G) (functor-op F) renaming (Comma-obj to Comma-obj′ ; [_,_,_] to [_,_,_]′ ; Comma-hom to Comma-hom′ ; Comma-homset to Comma-homset′ ; make-hom to make-hom′ ; Comma-id to Comma-id′)

  obv : Functor (opposite (Comma F G)) (Comma (functor-op G) (functor-op F))
  obv = makeFunctor obj hom id compose where
    obj : Comma-obj → Comma-obj′
    obj [ a , b , f ] = [ b , a , f ]′

    homset : {x y : Comma-obj} → Comma-homset x y → Comma-homset′ (obj y) (obj x)
    homset (make-hom g f ε) = make-hom′ f g (≈-sym ε)

    hom : {x y : Comma-obj} → Comma-hom x y ⟶ Comma-hom′ (obj y) (obj x)
    hom {x} {y} = record {
      _⟨$⟩_ = homset;
      cong = swap }

    id : (x : Comma-obj) → _
    id x = Category.≈-refl B ,′ Category.≈-refl A

    compose : {x y z : Comma-obj} (g : Comma-homset x y) (f : Comma-homset y z) → _
    compose g f = Category.≈-refl B ,′ Category.≈-refl A

  rev : Functor (Comma (functor-op G) (functor-op F)) (opposite (Comma F G))
  rev = makeFunctor obj hom id compose where
    obj : Comma-obj′ → Comma-obj
    obj [ a , b , f ]′ = [ b , a , f ]

    homset : {x y : Comma-obj′} → Comma-homset′ x y → Comma-homset (obj y) (obj x)
    homset (make-hom′ g f ε) = make-hom f g (≈-sym ε)

    hom : {x y : Comma-obj′} → Comma-hom′ x y ⟶ Comma-hom (obj y) (obj x)
    hom {x} {y} = record {
      _⟨$⟩_ = homset;
      cong = swap }

    id : (x : Comma-obj′) → _
    id x = Category.≈-refl A ,′ Category.≈-refl B

    compose : {x y z : Comma-obj′} (g : Comma-homset′ y z) (f : Comma-homset′ x y) → _
    compose g f = Category.≈-refl A ,′ Category.≈-refl B

  unit : rev ⊙ obv ≅₁ idFunctor (opposite (Comma F G))
  unit = isomorphic₁ Φ Ψ u c where
    Φ : NatTrans (rev ⊙ obv) (idFunctor (opposite (Comma F G)))
    Φ = makeNatTrans Comma-id (λ f → Category.≈-trans A (Category.id-r A _) (Category.≈-sym A (Category.id-l A _)) ,′ Category.≈-trans B (Category.id-r B _) (Category.≈-sym B (Category.id-l B _)))
    Ψ : NatTrans (idFunctor (opposite (Comma F G))) (rev ⊙ obv)
    Ψ = makeNatTrans Comma-id (λ f → Category.≈-trans A (Category.id-r A _) (Category.≈-sym A (Category.id-l A _)) ,′ Category.≈-trans B (Category.id-r B _) (Category.≈-sym B (Category.id-l B _)))
    u : _ ≈₂ _
    u = make-≈₂ (λ x → Category.id-l A _ ,′ Category.id-l B _)
    c : _ ≈₂ _
    c = make-≈₂ (λ x → Category.id-l A _ ,′ Category.id-l B _)

  counit : obv ⊙ rev ≅₁ idFunctor (Comma (functor-op G) (functor-op F))
  counit = isomorphic₁ Θ Ξ u c where
    Θ : NatTrans (obv ⊙ rev) (idFunctor (Comma (functor-op G) (functor-op F)))
    Θ = makeNatTrans Comma-id′ (λ f → Category.≈-trans B (Category.id-r B _) (Category.≈-sym B (Category.id-l B _)) ,′ Category.≈-trans A (Category.id-r A _) (Category.≈-sym A (Category.id-l A _)))
    Ξ : NatTrans (idFunctor (Comma (functor-op G) (functor-op F))) (obv ⊙ rev)
    Ξ = makeNatTrans Comma-id′ (λ f → Category.≈-trans B (Category.id-r B _) (Category.≈-sym B (Category.id-l B _)) ,′ Category.≈-trans A (Category.id-r A _) (Category.≈-sym A (Category.id-l A _)))
    u : _ ≈₂ _
    u = make-≈₂ (λ x → Category.id-l B _ ,′ Category.id-l A _)
    c : _ ≈₂ _
    c = make-≈₂ (λ x → Category.id-l B _ ,′ Category.id-l A _)
