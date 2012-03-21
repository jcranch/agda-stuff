module Sheffield.CategoryTheory-Setoid.Terminal.Comparison where

open import Data.Unit using (tt)
open import Level
open import Relation.Binary

open import Sheffield.CategoryTheory-Setoid.Categories
open import Sheffield.CategoryTheory-Setoid.Categories.Diagrams
open import Sheffield.CategoryTheory-Setoid.Comma
open import Sheffield.CategoryTheory-Setoid.Functors
open import Sheffield.CategoryTheory-Setoid.Functors.Category
open import Sheffield.CategoryTheory-Setoid.Limits
open import Sheffield.CategoryTheory-Setoid.Terminal
open import Sheffield.CategoryTheory-Setoid.NaturalTransformations





empty-limit-is-terminal : {ℓ₂ ℓ′₂ ℓ″₂ : Level} {C : Category {ℓ₂} {ℓ′₂} {ℓ″₂}} (F : Functor ∅ C) (L : Category.obj (cones F)) (l : IsLimit F L) → IsTerminal C (IsLimit.object l)
empty-limit-is-terminal {C = C} F L l = record {
  exists = λ x → {!IsTerminal.exists (cones F) (IsLimit.limiting l)!} ;
  unique = λ f → {!!} }



-- fails to typecheck in Agda 2.3.0; typechecks fine in bleeding-edge as of 2012-02-17
terminal-is-empty-limit : {ℓ₂ ℓ′₂ ℓ″₂ : Level} {C : Category {ℓ₂} {ℓ′₂} {ℓ″₂}} (t : Category.obj C) (term : IsTerminal C t) → IsLimit {C = C} ∅-functor [ t , tt , ∅-nat-trans ]
terminal-is-empty-limit t term = {!!}
