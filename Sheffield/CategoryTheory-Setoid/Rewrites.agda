module Sheffield.CategoryTheory-Setoid.Rewrites where

open import Data.List
open import Data.Product
open import Level

open import Sheffield.CategoryTheory-Setoid.Categories
open import Sheffield.CategoryTheory-Setoid.Paths



data ∀-list {ℓ ℓ′ : Level} {A : Set ℓ} (P : A → Set ℓ′) : List A → Set (ℓ ⊔ ℓ′) where
  []′ : ∀-list P []
  _∷′_ : {h : A} {t : List A} → P h → ∀-list P t → ∀-list P (h ∷ t)




data List⁺ {ℓ : Level} (A : Set ℓ) : Set ℓ where
  one : A → List⁺ A
  cons : A → List⁺ A → List⁺ A

first : {ℓ : Level} {A : Set ℓ} → List⁺ A → A
first (one x) = x
first (cons h t) = h

last : {ℓ : Level} {A : Set ℓ} → List⁺ A → A
last (one x) = x
last (cons h t) = last t

consecutives : {ℓ : Level} {A : Set ℓ} → List⁺ A → List (A × A)
consecutives (one x) = []
consecutives (cons h t) = (h ,′ first t) ∷ consecutives t



module RewriteReasoning {ℓ ℓ′ ℓ″ : Level} (C : Category {ℓ} {ℓ′} {ℓ″}) where

  open Category C

  mutual

    data Rewriting : obj → obj → Set ? where
      stop : {x : obj} → Rewriting x x
      node : {x y : obj} → RNode x y → Rewriting x y

    record RNode {x y : obj} : Set ? where
      field
        list⁺ : List⁺ (REdge x y)
        joins : ∀-list RFace (consecutives list⁺)

    record REdge {x y : obj} : Set ? where
      constructor makeEdge
      field
        vertex : obj
        morphism : homset x vertex
        downstream : Rewriting vertex y
      
    data RFace {x y : obj} : REdge x y × REdge x y → Set ? where
      make-face : {j : obj} {α β : homset x j} {r : Rewriting j y} {E₁ E₂ : REdge x y} → Trail↓ E₁ α r → Trail↑ E₂ β r → RFace (E₁ ,′ E₂)
        
    data Trail↓ : {x j y : obj} → REdge x y → homset x j → Rewriting j y → Set ? where
      nil↓ : {x j y : obj} (f : homset x j) (d : Rewriting j y) → Trail↓ (makeEdge j f d) f d
      cons↓ : 

    data Trail↑ : {x j y : obj} → REdge x y → homset x j → Rewriting j y → Set ? where
      nil↑ : {x j y : obj} (f : homset x j) (d : Rewriting j y) → Trail↑ (makeEdge j f d) f d

{-
  topend : {x y : obj} → Rewriting x y → Path x y
  topend {x} {.x} stop = finish
  topend {x} {y} (node n) = ?

  bottomend : {x y : obj} → Rewriting x y → Path x y
  bottomend {x} {.x} stop = finish
  bottomend {x} {y} (node n) = ?
-}