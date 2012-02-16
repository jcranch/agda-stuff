module Sheffield.CategoryTheory-Set.Examples.Matrix.VectorExtra where

open import Data.Vec
open import Data.Fin
import Relation.Binary.PropositionalEquality as PropEq
open import Relation.Binary.Core using (_≡_ ; refl)

lookup-≡ : ∀ {a} {A : Set a} {n} (xs ys : Vec A n)
           → (p : (i : Fin n) → lookup i xs ≡ lookup i ys)
           → xs ≡ ys
lookup-≡ [] [] p = refl
lookup-≡ (x ∷ xs) (y ∷ ys) p = PropEq.cong₂ _∷_ (p zero) (lookup-≡ xs ys (λ i → p (suc i)))

