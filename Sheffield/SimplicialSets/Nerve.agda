module Sheffield.SimplicialSets.Nerve where

open import Level

open import Sheffield.CategoryTheory-Setoid.Categories
open import Sheffield.CategoryTheory-Setoid.Categories.Equivalence
open import Sheffield.CategoryTheory-Setoid.Examples.Sets
open import Sheffield.CategoryTheory-Setoid.Examples.Categories
open import Sheffield.CategoryTheory-Setoid.Functors
open import Sheffield.CategoryTheory-Setoid.Functors.Category
open import Sheffield.CategoryTheory-Setoid.Functors.Yoneda

open import Sheffield.SimplicialSets.Simplicial
open import Sheffield.SimplicialSets.Simplicial.Categorical


-- Fails for level reasons. So close...


nerve : Functor Categories (simplicial Setoids)
nerve = {!yoneda Categories ⊙ Δ→Cat!}
