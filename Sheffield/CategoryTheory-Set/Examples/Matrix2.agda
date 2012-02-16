-- An alternative implementation of matrices

module Sheffield.CategoryTheory-Set.Examples.Matrix2 where

open import Algebra
open import Algebra.Structures
open import Data.Nat
open import Data.Product hiding (map)
open import Data.Vec
open import Function
open import Level hiding (suc)
open import Relation.Binary.PropositionalEquality


private
  cong₄ : ∀ {a b c d e} {A : Set a} {B : Set b} {C : Set c} {D : Set d} {E : Set e} (f : A → B → C → D → E) {x y u v p q m n} → x ≡ y → u ≡ v → p ≡ q → m ≡ n → f x u p m ≡ f y v q n
  cong₄ f refl refl refl refl = refl




module matrix-algebra {c : Level} {∣A∣ : Set c}
  {_+_ : ∣A∣ → ∣A∣ → ∣A∣} {_*_ : ∣A∣ → ∣A∣ → ∣A∣} {−_ : ∣A∣ → ∣A∣} {0# : ∣A∣} {1# : ∣A∣}
  (isRing : IsRing _≡_ _+_ _*_ −_ 0# 1#) where

  A : Ring c c
  A = record { isRing = isRing }
  open Ring A hiding (refl ; sym ; trans) renaming (zero to zero-law)


  data Mat : ℕ → ℕ → Set c where
    nil₀₀ : Mat 0 0
    nil₀₋ : {n : ℕ} → Mat 0 (suc n)
    nil₋₀ : {n : ℕ} → Mat (suc n) 0
    mat : {m n : ℕ} (x₀₀ : ∣A∣) (x₋₀ : Vec ∣A∣ m) (x₀₋ : Vec ∣A∣ n) (x₋₋ : Mat m n) → Mat (suc m) (suc n)


  -- affix a row
  vcons : {m n : ℕ} → Vec ∣A∣ n → Mat m n → Mat (suc m) n
  vcons [] M = nil₋₀
  vcons (x ∷ []) nil₀₋ = mat x [] [] nil₀₀
  vcons (x₁ ∷ x₂ ∷ xs) nil₀₋ = mat x₁ [] (x₂ ∷ xs) nil₀₋
  vcons (x ∷ xs) (mat x₀₀ x₋₀ x₀₋ x₋₋) = mat x (x₀₀ ∷ x₋₀) xs (vcons x₀₋ x₋₋)

  -- affix a column
  hcons : {m n : ℕ} → Vec ∣A∣ m → Mat m n → Mat m (suc n)
  hcons [] M = nil₀₋
  hcons (x ∷ []) nil₋₀ = mat x [] [] nil₀₀
  hcons (x₁ ∷ x₂ ∷ xs) nil₋₀ = mat x₁ (x₂ ∷ xs) [] nil₋₀
  hcons (x ∷ xs) (mat x₀₀ x₋₀ x₀₋ x₋₋) = mat x xs (x₀₀ ∷ x₀₋) (hcons x₋₀ x₋₋)


  rows : {m n : ℕ} → Mat m n → Vec (Vec ∣A∣ n) m
  rows nil₀₀ = []
  rows nil₀₋ = []
  rows nil₋₀ = replicate []
  rows (mat x₀₀ x₋₀ x₀₋ x₋₋) = (x₀₀ ∷ x₀₋) ∷ zipWith _∷_ x₋₀ (rows x₋₋)


  columns : {m n : ℕ} → Mat m n → Vec (Vec ∣A∣ m) n
  columns nil₀₀ = []
  columns nil₀₋ = replicate []
  columns nil₋₀ = []
  columns (mat x₀₀ x₋₀ x₀₋ x₋₋) = (x₀₀ ∷ x₋₀) ∷ zipWith _∷_ x₀₋ (columns x₋₋)


  transpose : {m n : ℕ} → Mat m n → Mat n m
  transpose nil₀₀ = nil₀₀
  transpose nil₀₋ = nil₋₀
  transpose nil₋₀ = nil₀₋
  transpose (mat x₀₀ x₋₀ x₀₋ x₋₋) = mat x₀₀ x₀₋ x₋₀ (transpose x₋₋)


  zipWith² : {a b : Level} {S : Set a} {T : Set b} {m n : ℕ} (f : S → T → ∣A∣) → Vec S m → Vec T n → Mat m n
  zipWith² f [] [] = nil₀₀
  zipWith² f [] (y ∷ ys) = nil₀₋
  zipWith² f (x ∷ xs) [] = nil₋₀
  zipWith² f (x ∷ xs) (y ∷ ys) = mat (f x y) (map (flip f y) xs) (map (f x) ys) (zipWith² f xs ys)


  zero-matrix : {m n : ℕ} → Mat m n
  zero-matrix {ℕ.zero} {ℕ.zero} = nil₀₀
  zero-matrix {ℕ.zero} {suc n} = nil₀₋
  zero-matrix {suc m} {ℕ.zero} = nil₋₀
  zero-matrix {suc m} {suc n} = mat 0# (replicate 0#) (replicate 0#) zero-matrix

  id-matrix : (n : ℕ) → Mat n n
  id-matrix ℕ.zero = nil₀₀
  id-matrix (suc n) = mat 1# (replicate 0#) (replicate 0#) (id-matrix n)

  ⟨_,_⟩ : {n : ℕ} → Vec ∣A∣ n → Vec ∣A∣ n → ∣A∣
  ⟨ [] , [] ⟩ = 0#
  ⟨ x ∷ xs , y ∷ ys ⟩ = (x * y) + ⟨ xs , ys ⟩

  inner-zeroˡ : {n : ℕ} (v : Vec ∣A∣ n) → ⟨ replicate 0# , v ⟩ ≡ 0#
  inner-zeroˡ [] = refl
  inner-zeroˡ (x ∷ xs) = trans (+-cong (proj₁ zero-law x) (inner-zeroˡ xs)) (proj₁ +-identity 0#)

  _✶_ : {l m n : ℕ} → Mat l m → Mat m n → Mat l n
  M ✶ N = zipWith² ⟨_,_⟩ (rows M) (columns N)

{-
  ✶-id-l : {m n : ℕ} (M : Mat m n) → id-matrix m ✶ M ≡ M
  ✶-id-l nil₀₀ = refl
  ✶-id-l nil₀₋ = refl
  ✶-id-l nil₋₀ = refl
  ✶-id-l (mat x₀₀ x₋₀ x₀₋ x₋₋) = cong₄ mat (trans (+-cong (proj₁ *-identity x₀₀) (inner-zeroˡ x₋₀)) (proj₂ +-identity x₀₀)) {!!} {!!} {!!}
-}