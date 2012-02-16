module Sheffield.CategoryTheory-Set.Adjunctions where

open import Level
open import Relation.Binary.PropositionalEquality

open import Sheffield.CategoryTheory-Set.Categories
open import Sheffield.CategoryTheory-Set.Functors
open import Sheffield.CategoryTheory-Set.NaturalTransformations
open import Sheffield.CategoryTheory-Set.NaturalTransformations.Equality


record Adjunction {α α′ β β′ : Level} {C : Category {α} {α′}} {D : Category {β} {β′}} (left : Functor D C) (right : Functor C D) : Set (α ⊔ α′ ⊔ β ⊔ β′) where
  constructor makeAdjunction
  field
    counit : NatTrans (left ⊙ right) (idFunctor C)
    unit : NatTrans (idFunctor D) (right ⊙ left)
    counit-unit₁ : (y : Category.obj D) → Category.compose C (NatTrans.component counit (Functor.obj left y)) (Functor.hom left (NatTrans.component unit y)) ≡ Category.id C (Functor.obj left y)
    counit-unit₂ : (x : Category.obj C) → Category.compose D (Functor.hom right (NatTrans.component counit x)) (NatTrans.component unit (Functor.obj right x)) ≡ Category.id D (Functor.obj right x)
-- can't make the following preferred definitions work, since the equalities of types are too subtle
{-
    counit-unit₁ : (counit ⊙̂ idNatTrans left) •̂ (idNatTrans left ⊙̂ unit) ≡₂ idNatTrans left
    counit-unit₂ : (idNatTrans right ⊙̂ counit) •̂ (counit ⊙̂ idNatTrans right) ≡₂ idNatTrans right
-}

⊣ : {α α′ β β′ : Level} {C : Category {α} {α′}} {D : Category {β} {β′}} (left : Functor D C) (right : Functor C D) → Set (α ⊔ α′ ⊔ β ⊔ β′)
⊣ = Adjunction


-- adjunctions and opposites

-- uniqueness results: any two adjunctions involving the same functor as left or as right are isomorphic

-- chains of adjunctions give adjunctions of the composites