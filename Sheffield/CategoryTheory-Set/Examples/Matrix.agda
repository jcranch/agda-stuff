module Sheffield.CategoryTheory-Set.Examples.Matrix where


-- this code is not computationally particularly efficient
-- one could replace the matrix algorithms with provably equivalent recursive strategies, but it's probably best to use built-in technology


open import Algebra
open import Algebra.Structures
open import Data.Empty
open import Data.Fin using (Fin) renaming (zero to fzero ; suc to fsuc)
open import Data.Fin.Props using (strictTotalOrder ; _≟_)
open import Data.Nat hiding (_+_ ; _*_ ; _≟_)
open import Data.Product using (proj₁ ; proj₂)
import Data.Vec as V
import Data.Vec.Properties as V
open import Function
open import Level hiding (zero ; suc)
open import Relation.Binary
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary.Core
open ≡-Reasoning

open import Sheffield.CategoryTheory-Set.Categories
import Sheffield.CategoryTheory-Set.Examples.Matrix.VectorExtra as V


if_then_else : {ℓ ℓ′ : Level} {P : Set ℓ} {Q : Set ℓ′} → Dec P → Q → Q → Q
if_then_else (yes p) x y = x
if_then_else (no ¬p) x y = y


module matrix-algebra {c : Level} {∣A∣ : Set c}
  {_+_ : ∣A∣ → ∣A∣ → ∣A∣} {_*_ : ∣A∣ → ∣A∣ → ∣A∣} {−_ : ∣A∣ → ∣A∣} {0# : ∣A∣} {1# : ∣A∣}
  (isRing : IsRing _≡_ _+_ _*_ −_ 0# 1#) where

  A : Ring c c
  A = record { isRing = isRing }
  open Ring A hiding (refl ; sym ; trans) renaming (zero to zero-law)


  -- matrices as functions
  module F where

    infixr 7 _✶_
    infix 4 _≣_

    -- sums over maps Fin n → ∣A∣
    Σ : {n : ℕ} → (Fin n → ∣A∣) → ∣A∣
    Σ {zero} f = 0#
    Σ {suc n} f = f fzero + Σ (f ∘ fsuc)

    Σ-cong : {n : ℕ} {f g : Fin n → ∣A∣} → ((i : Fin n) → f i ≡ g i) → Σ f ≡ Σ g
    Σ-cong {zero} {f} {g} E = refl
    Σ-cong {suc n} {f} {g} E = cong₂ _+_ (E fzero) (Σ-cong {n} {f ∘ fsuc} {g ∘ fsuc} (E ∘ fsuc))

    Σ-zero : (n : ℕ) → Σ {n} (λ _ → 0#) ≡ 0#
    Σ-zero (zero) = refl
    Σ-zero (suc n) = trans (proj₁ +-identity _) (Σ-zero n)

    Σ-distributes-over-+ : {n : ℕ} (f g : Fin n → ∣A∣) → Σ (λ i → f i + g i) ≡ (Σ f) + (Σ g)
    Σ-distributes-over-+ {zero} f g = sym (proj₁ +-identity _)
    Σ-distributes-over-+ {suc n} f g = begin
      (f fzero + g fzero) + Σ (λ x → f (fsuc x) + g (fsuc x))
        ≡⟨ cong (_+_ _) (Σ-distributes-over-+ (f ∘ fsuc) (g ∘ fsuc)) ⟩
      (f fzero + g fzero) + ((Σ (f ∘ fsuc)) + (Σ (g ∘ fsuc)))
        ≡⟨ +-assoc _ _ _ ⟩
      f fzero + (g fzero + ((Σ (f ∘ fsuc)) + (Σ (g ∘ fsuc))))
        ≡⟨ cong (_+_ (f fzero)) (sym (+-assoc _ _ _)) ⟩
      f fzero + ((g fzero + Σ (f ∘ fsuc)) + Σ (g ∘ fsuc))
        ≡⟨ cong (λ α → (f fzero + (α + Σ (g ∘ fsuc)))) (+-comm _ _) ⟩
      f fzero + (((Σ (f ∘ fsuc)) + g fzero) + Σ (g ∘ fsuc))
        ≡⟨ cong (_+_ (f fzero)) (+-assoc _ _ _) ⟩
      f fzero + ((Σ (f ∘ fsuc)) + (g fzero + Σ (g ∘ fsuc)))
        ≡⟨ sym (+-assoc _ _ _) ⟩
      (f fzero + Σ (f ∘ fsuc)) + (g fzero + Σ (g ∘ fsuc)) ∎

    Σ-exchange : {m n : ℕ} (f : Fin m → Fin n → ∣A∣) → Σ (λ i → Σ (f i)) ≡ Σ (λ j → Σ (flip f j))
    Σ-exchange {zero} {n} f = sym (Σ-zero n)
    Σ-exchange {suc m} {n} f = trans (cong (_+_ (Σ (f fzero))) (Σ-exchange (λ i j → f (fsuc i) j))) (sym (Σ-distributes-over-+ (f fzero) (λ j → Σ (λ x → f (fsuc x) j))))

    *-distributes-over-Σˡ : {n : ℕ} (a : ∣A∣) (f : Fin n → ∣A∣) → a * Σ f ≡ Σ (_*_ a ∘ f)
    *-distributes-over-Σˡ {zero} a f = proj₂ zero-law a
    *-distributes-over-Σˡ {suc n} a f = begin
      a * (f fzero + Σ (λ x → f (fsuc x)))
        ≡⟨ proj₁ distrib a (f fzero) (Σ (λ x → f (fsuc x))) ⟩
      (a * f fzero) + (a * Σ (λ x → f (fsuc x)))
        ≡⟨ cong (_+_ (a * f fzero)) (*-distributes-over-Σˡ a (f ∘ fsuc)) ⟩
      (a * f fzero) + Σ (λ x → a * f (fsuc x)) ∎

    *-distributes-over-Σʳ : {n : ℕ} (a : ∣A∣) (f : Fin n → ∣A∣) → (Σ f) * a ≡ Σ (flip _*_ a ∘ f)
    *-distributes-over-Σʳ {zero} a f = proj₁ zero-law a
    *-distributes-over-Σʳ {suc n} a f = begin
      (f fzero + Σ (λ x → f (fsuc x))) * a
        ≡⟨ proj₂ distrib a (f fzero) (Σ (λ x → f (fsuc x))) ⟩
      (f fzero * a) + (Σ (λ x → f (fsuc x)) * a)
        ≡⟨ cong (_+_ (f fzero * a)) (*-distributes-over-Σʳ a (f ∘ fsuc)) ⟩
      (f fzero * a) + Σ (λ x → f (fsuc x) * a) ∎

    Σ-one-nonzeroˡ : {n : ℕ} (a : ∣A∣) (i : Fin n) → Σ (λ j → if (i ≟ j) then a else 0#) ≡ a
    Σ-one-nonzeroˡ {zero} a ()
    Σ-one-nonzeroˡ {suc n} a fzero = trans (cong (_+_ a) (Σ-zero n)) (proj₂ +-identity a)
    Σ-one-nonzeroˡ {suc n} a (fsuc i) = trans (proj₁ +-identity _) (trans (Σ-cong {n} (λ j → k j)) (Σ-one-nonzeroˡ {n} a i)) where
      k : (j : Fin n) → ((λ j' → if fsuc i ≟ j' then a else 0#) ∘ fsuc) j ≡ if i ≟ j then a else 0#
      k j with StrictTotalOrder.compare (strictTotalOrder n) i j | StrictTotalOrder.compare (strictTotalOrder (suc n)) (fsuc i) (fsuc j)
      k j | tri< a' ¬b ¬c | tri< a0 ¬b' ¬c' = refl
      k j | tri< a' ¬b ¬c | tri≈ ¬a b ¬c' = ⊥-elim (¬a (s≤s a'))
      k j | tri< a' ¬b ¬c | tri> ¬a ¬b' c' = refl
      k j | tri≈ ¬a b ¬c | tri< a' ¬b ¬c' = ⊥-elim (¬b (cong fsuc b))
      k j | tri≈ ¬a b ¬c | tri≈ ¬a' b' ¬c' = refl
      k j | tri≈ ¬a b ¬c | tri> ¬a' ¬b c' = ⊥-elim (¬b (cong fsuc b))
      k j | tri> ¬a ¬b c' | tri< a' ¬b' ¬c = refl
      k j | tri> ¬a ¬b c' | tri≈ ¬a' b ¬c = ⊥-elim (¬c (s≤s c'))
      k j | tri> ¬a ¬b c' | tri> ¬a' ¬b' c0 = refl

    Σ-one-nonzeroʳ : {n : ℕ} (a : ∣A∣) (i : Fin n) → Σ (λ j → if (j ≟ i) then a else 0#) ≡ a
    Σ-one-nonzeroʳ {n} a i = trans (Σ-cong {n} f) (Σ-one-nonzeroˡ {n} a i) where
      f : (j : Fin n) → if j ≟ i then a else 0# ≡ if i ≟ j then a else 0#
      f j with (StrictTotalOrder.compare (strictTotalOrder n) i j) | (StrictTotalOrder.compare (strictTotalOrder n) j i)
      f j | tri< a' ¬b ¬c | tri< a0 ¬b' ¬c' = refl
      f j | tri< a' ¬b ¬c | tri≈ ¬a b ¬c' = ⊥-elim (¬c' a')
      f j | tri< a' ¬b ¬c | tri> ¬a ¬b' c' = refl
      f j | tri≈ ¬a b ¬c | tri< a' ¬b ¬c' = ⊥-elim (¬b (sym b))
      f j | tri≈ ¬a b ¬c | tri≈ ¬a' b' ¬c' = refl
      f j | tri≈ ¬a b ¬c | tri> ¬a' ¬b c' = ⊥-elim (¬b (sym b))
      f j | tri> ¬a ¬b c' | tri< a' ¬b' ¬c = refl
      f j | tri> ¬a ¬b c' | tri≈ ¬a' b ¬c = ⊥-elim (¬a' c')
      f j | tri> ¬a ¬b c' | tri> ¬a' ¬b' c0 = refl

    


    data Matrix (m n : ℕ) : Set c where
      make-matrix : (Fin m → Fin n → ∣A∣) → Matrix m n



    lookup : {m n : ℕ} → Matrix m n → Fin m → Fin n → ∣A∣
    lookup (make-matrix A) i j = A i j

    _≣_ : {m n : ℕ} → Matrix m n → Matrix m n → Set c
    _≣_ {m} {n} A B = (i : Fin m) (j : Fin n) → lookup A i j ≡ lookup B i j

    --function operations
    transpose : {m n : ℕ} → Matrix m n → Matrix n m
    transpose (make-matrix A) = make-matrix (flip A)

    id-matrix : (n : ℕ) → Matrix n n
    id-matrix n = make-matrix (λ i j → if (i ≟ j) then 1# else 0#)

    _✶_ : {l m n : ℕ} → Matrix l m → Matrix m n → Matrix l n
    (make-matrix A ✶ make-matrix B) = make-matrix (λ i k → Σ (λ j → A i j * B j k))

    ✶-id-l : {m n : ℕ} (M : Matrix m n) → (id-matrix m) ✶ M ≣ M
    ✶-id-l {m} {n} (make-matrix M) = λ i j → trans (Σ-cong {m} (λ k → f i j k)) (Σ-one-nonzeroˡ (M i j) i) where
      f : ∀ i j k → if i ≟ k then 1# else 0# * M k j ≡ if i ≟ k then M i j else 0#
      f i j k with StrictTotalOrder.compare (strictTotalOrder m) i k
      f i j k | tri< a ¬b ¬c = proj₁ zero-law (M k j)
      f i j .i | tri≈ ¬a refl ¬c = proj₁ *-identity (M i j)
      f i j k | tri> ¬a ¬b c' = proj₁ zero-law (M k j)

    ✶-id-r : {m n : ℕ} (M : Matrix m n) → M ✶ (id-matrix n) ≣ M
    ✶-id-r {m} {n} (make-matrix M) = λ i j → trans (Σ-cong {n} (λ k → f i j k)) (Σ-one-nonzeroʳ (M i j) j) where
      f : ∀ i j k → M i k * (if k ≟ j then 1# else 0#) ≡ if k ≟ j then M i j else 0#
      f i j k with StrictTotalOrder.compare (strictTotalOrder n) k j
      f i j k | tri< a ¬b ¬c = proj₂ zero-law (M i k)
      f i j .j | tri≈ ¬a refl ¬c = proj₂ *-identity (M i j)
      f i j k | tri> ¬a ¬b c' = proj₂ zero-law (M i k)

    ✶-assoc : {m₁ m₂ m₃ m₄ : ℕ} (A : Matrix m₁ m₂) (B : Matrix m₂ m₃) (C : Matrix m₃ m₄) → A ✶ (B ✶ C) ≣ (A ✶ B) ✶ C
    ✶-assoc (make-matrix A) (make-matrix B) (make-matrix C) = λ i l → begin
      Σ (λ j → A i j * Σ (λ k → B j k * C k l))
        ≡⟨ Σ-cong (λ j → *-distributes-over-Σˡ (A i j) (λ k → B j k * C k l)) ⟩
      Σ (λ j → Σ (λ k → A i j * (B j k * C k l)))
        ≡⟨ Σ-exchange (λ j k → A i j * (B j k * C k l)) ⟩
      Σ (λ k → Σ (λ j → A i j * (B j k * C k l)))
        ≡⟨ Σ-cong (λ k → Σ-cong (λ j → sym (*-assoc (A i j) (B j k) (C k l)))) ⟩
      Σ (λ k → Σ (λ j → (A i j * B j k) * C k l))
        ≡⟨ Σ-cong (λ k → sym (*-distributes-over-Σʳ (C k l) (λ j → A i j * B j k))) ⟩
      Σ (λ k → Σ (λ j → A i j * B j k) * C k l) ∎


  -- matrices as vectors of vectors
  module M where
  
    infixr 7 _✶_
    infixr 7 _✶′_
    _✶′_ = λ {l} {m} {n} → F._✶_ {l} {m} {n}

    data Matrix (m n : ℕ) : Set c where
      make-matrix : V.Vec (V.Vec ∣A∣ n) m → Matrix m n

    lookup : {m n : ℕ} → Matrix m n → F.Matrix m n
    lookup (make-matrix M) = F.make-matrix (λ i j → V.lookup j (V.lookup i M))

    tabulate : {m n : ℕ} → F.Matrix m n → Matrix m n
    tabulate (F.make-matrix f) = make-matrix (V.tabulate (λ i → V.tabulate (λ j → f i j)))

    lookup∘tabulate : {m n : ℕ} (M : F.Matrix m n) (i : Fin m) (j : Fin n) → F.lookup (lookup (tabulate M)) i j ≡ F.lookup M i j
    lookup∘tabulate (F.make-matrix f) i j = begin
      V.lookup j (V.lookup i (V.tabulate (λ i' → V.tabulate (f i'))))
        ≡⟨ cong (V.lookup j) (V.lookup∘tabulate (λ i' → V.tabulate (f i')) i) ⟩
      V.lookup j (V.tabulate (f i))
        ≡⟨ V.lookup∘tabulate (f i) j ⟩
      f i j ∎ where open ≡-Reasoning

    lookup-≡ : {m n : ℕ} {M₁ M₂ : Matrix m n} → F._≣_ (lookup M₁) (lookup M₂) → M₁ ≡ M₂
    lookup-≡ {m} {n} {make-matrix M₁} {make-matrix M₂} e = cong make-matrix (V.lookup-≡ M₁ M₂ (λ i → V.lookup-≡ (V.lookup i M₁) (V.lookup i M₂) (e i)))

    id-matrix : (n : ℕ) → Matrix n n
    id-matrix n = tabulate (F.id-matrix n)
    
    _✶_ : {l m n : ℕ} → Matrix l m → Matrix m n → Matrix l n
    M ✶ N = tabulate ((lookup M) ✶′ (lookup N))

{-
    ✶-id-l : {m n : ℕ} (M : Matrix m n) → (id-matrix m) ✶ M ≡ M
    ✶-id-l {m} {n} M = lookup-≡ (λ i j → trans {!!} (F.✶-id-l (lookup M) i j))
-}

{-
    ✶-id-r : {m n : ℕ} (M : Matrix m n) → M ✶ (id-matrix n) ≡ M
    ✶-id-r {m} {n} M = {!!}
-}

{-
    ✶-assoc : {m₁ m₂ m₃ m₄ : ℕ} (A : Matrix m₁ m₂) (B : Matrix m₂ m₃) (C : Matrix m₃ m₄) → A ✶ (B ✶ C) ≡ (A ✶ B) ✶ C
    ✶-assoc A B C = {!!}
-}

{-      
 
  free-module-category : Category
  free-module-category = record {
    obj = ℕ ;
    hom = Matrix ; 
    id = id-matrix ;
    compose = flip _✶_ ;
    id-l = {!!} ;
    id-r = {!!} ;
    assoc = {!!} }

  -- build an abelian enrichment too

-}