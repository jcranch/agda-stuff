module Sheffield.CategoryTheory-Setoid.Examples.Simplex where

open import Data.Fin
open import Data.Nat hiding (_≤_)
open import Level
open import Relation.Binary
open import Relation.Binary.PropositionalEquality using (refl)

open import Sheffield.CategoryTheory-Setoid.Categories
open import Sheffield.CategoryTheory-Setoid.Examples.PreorderCategory

simplex : ℕ → Category {Level.zero} {Level.zero} {Level.zero}
simplex n = PreorderCategory (_≤_ {n}) (DecTotalOrder.reflexive decTotalOrder refl) (DecTotalOrder.trans decTotalOrder)

module arrow-category where

  arrow : Category
  arrow = simplex 2

  s : Fin 2
  s = Fin.zero

  t : Fin 2
  t = Fin.suc Fin.zero

  s→t : Category.homset arrow s t
  s→t = z≤n
