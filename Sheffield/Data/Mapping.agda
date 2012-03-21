module Mapping where

open import Category.Monad
open import Data.Bool
open import Data.Empty using (⊥-elim)
open import Data.List hiding (map ; filter ; monad)
open import Data.Maybe using (maybe′ ; monad)
open import Data.Maybe.Core
open import Data.Nat hiding (_⊔_ ; fold)
open import Data.Product hiding (map)
open import Data.Unit
open import Function using (const ; id ; _∘_)
open import Level hiding (zero ; suc)
open import Relation.Binary.Core using (Decidable)
open import Relation.Binary.PropositionalEquality renaming ([_] to ⟨_⟩)
open import Relation.Nullary.Core using (Dec ; yes ; no)





-- there is a standard library function, with the unacceptably short name of "T",
-- but I prefer this since it can be matched against
data isTrue : Bool → Set where
  true✓ : isTrue true



record MapClass {κ ν ℓ : Level} (K : Set κ) (_≟_ : Decidable {A = K} _≡_) : Set (Level.suc (κ ⊔ ν ⊔ ℓ)) where

  field
    Map    : (V : K → Set ν) → Set ℓ

    nonempty? : {V : K → Set ν} → Map V → Bool

    size : {V : K → Set ν} → Map V → ℕ
    nonempty?-size0 : {V : K → Set ν} (M : Map V) → if nonempty? M then size M > 0 else size M ≡ 0

    lookup : {V : K → Set ν} → Map V → (k : K) → Maybe (V k)

    empty : {V : K → Set ν} → Map V
    lookup-empty : {V : K → Set ν} (k : K) → lookup {V} empty k ≡ nothing

    -- alter the value of a certain key
    alter : {V : K → Set ν} (k : K) (f : Maybe (V k) → Maybe (V k)) → Map V → Map V
    lookup-alter-new : {V : K → Set ν} (k : K) (f : Maybe (V k) → Maybe (V k)) (M : Map V) → lookup (alter k f M) k ≡ f (lookup M k)
    lookup-alter-old : {V : K → Set ν} (k k′ : K) (f : Maybe (V k) → Maybe (V k)) (M : Map V) → k ≢ k′ → lookup (alter k f M) k′ ≡ lookup M k′

    -- mapfilter
    mapfilter : {V V′ : K → Set ν} → ((k : K) → V k → Maybe (V′ k)) → Map V → Map V′
    lookup-mapfilter : {V V′ : K → Set ν} (f : (k : K) → V k → Maybe (V′ k)) (M : Map V) (k : K) → lookup (mapfilter f M) k ≡ maybe′ (f k) nothing (lookup M k)

    -- combine
    -- the "swiss army knife" of binary map combinators
    combine : {V₁ V₂ V : K → Set ν} (f : (k : K) → Maybe (V₁ k) → Maybe (V₂ k) → Maybe (V k)) → Map V₁ → Map V₂ → Map V
    lookup-combine : {V₁ V₂ V : K → Set ν} → (f : (k : K) → Maybe (V₁ k) → Maybe (V₂ k) → Maybe (V k)) (M₁ : Map V₁) (M₂ : Map V₂) (k : K) → lookup (combine f M₁ M₂) k ≡ f k (lookup M₁ k) (lookup M₂ k)

    -- fold
    fold : {V : K → Set ν} {A : Set (κ ⊔ ν)} (z : A) (s : Σ K V → A → A) → Map V → A

  open RawMonad {ν} monad

  empty? : {V : K → Set ν} → Map V → Bool
  empty? M = not (nonempty? M)

  nonempty!  : {V : K → Set ν} → Map V → Set
  nonempty! M = isTrue (nonempty? M)

  -- extensional equality
  infix 4 _≡′_
  _≡′_ : {V : K → Set ν} → Map V → Map V → Set (κ ⊔ ν)
  M₁ ≡′ M₂ = (k : K) → lookup M₁ k ≡ lookup M₂ k

  ≡′-refl : {V : K → Set ν} (M : Map V) → M ≡′ M
  ≡′-refl {V} M k = refl

  ≡′-sym : {V : K → Set ν} {M N : Map V} → M ≡′ N → N ≡′ M
  ≡′-sym {V} {M} {N} M≡′N k = sym (M≡′N k)

  ≡′-trans : {V : K → Set ν} {L M N : Map V} → L ≡′ M → M ≡′ N → L ≡′ N
  ≡′-trans {V} {L} {M} {N} L≡′M M≡′N k = trans (L≡′M k) (M≡′N k)

    -- update or insert
  upsert : {V : K → Set ν} (k : K) (v : V k) → Map V → Map V
  upsert k v = alter k (const (just v))

  lookup-upsert-new : {V : K → Set ν} (k : K) (v : V k) (M : Map V) → lookup (upsert k v M) k ≡ just v
  lookup-upsert-new {V} k v = lookup-alter-new k (const (just v))

  lookup-upsert-old : {V : K → Set ν} (k k′ : K) (v : V k) (M : Map V) → k ≢ k′ → lookup (upsert k v M) k′ ≡ lookup M k′
  lookup-upsert-old {V} k k′ v = lookup-alter-old k k′ (const (just v))

    -- delete (if present)
  delete : {V : K → Set ν} (k : K) → Map V → Map V
  delete k = alter k (const nothing)

  lookup-delete-new : {V : K → Set ν} (k : K) (M : Map V) → lookup (delete k M) k ≡ nothing
  lookup-delete-new {V} k = lookup-alter-new k (const nothing)

  lookup-delete-old : {V : K → Set ν} (k k′ : K) (M : Map V) → k ≢ k′ → lookup (delete k M) k′ ≡ lookup M k′
  lookup-delete-old k k′ = lookup-alter-old k k′ (const nothing)

  -- singleton maps
  singleton : {V : K → Set ν} (k : K) (v : V k) → Map V
  singleton k v = upsert k v empty

  -- is k a key in M?
  is-member? : {V : K → Set ν} → Map V → (k : K) → Bool
  is-member? M k with lookup M k
  ... | nothing = false
  ... | just _ = true

  -- lookup with default
  lookup-default : {V : K → Set ν} → Map V → (k : K) (d : V k) → V k
  lookup-default M k d with lookup M k
  ... | nothing = d
  ... | just x = x

  -- basic properties of alter
  alter-id : {V : K → Set ν} (k : K) (M : Map V) → alter k id M ≡′ M
  alter-id {V} k M k′ with k ≟ k′
  ... | yes p = subst (λ x → lookup (alter k id M) x ≡ lookup M x) p (lookup-alter-new k id M)
  ... | no ¬p = lookup-alter-old k k′ id M ¬p

  alter-compose : {V : K → Set ν} (k : K) (g f : Maybe (V k) → Maybe (V k)) (M : Map V) → alter k g (alter k f M) ≡′ alter k (g ∘ f) M
  alter-compose {V} k g f M k′ with k ≟ k′
  ... | yes p = subst (λ x → lookup (alter k g (alter k f M)) x ≡ lookup (alter k (g ∘ f) M) x) p e where
        open ≡-Reasoning
        e = begin
          lookup (alter k g (alter k f M)) k
            ≡⟨ lookup-alter-new k g (alter k f M) ⟩
          g (lookup (alter k f M) k)
            ≡⟨ cong g (lookup-alter-new k f M) ⟩
          g (f (lookup M k))
            ≡⟨ sym (lookup-alter-new k (g ∘ f) M) ⟩
          lookup (alter k (g ∘ f) M) k ∎
  ... | no ¬p = begin
          lookup (alter k g (alter k f M)) k′
            ≡⟨ lookup-alter-old k k′ g (alter k f M) ¬p ⟩
          lookup (alter k f M) k′
            ≡⟨ lookup-alter-old k k′ f M ¬p ⟩
          lookup M k′
            ≡⟨ sym (lookup-alter-old k k′ (g ∘ f) M ¬p) ⟩
          lookup (alter k (g ∘ f) M) k′ ∎ where open ≡-Reasoning

  alter-commute : {V : K → Set ν} (k₁ k₂ : K) (f₁ : Maybe (V k₁) → Maybe (V k₁)) (f₂ : Maybe (V k₂) → Maybe (V k₂)) (M : Map V) → k₁ ≢ k₂ → alter k₁ f₁ (alter k₂ f₂ M) ≡′ alter k₂ f₂ (alter k₁ f₁ M)
  alter-commute {V} k₁ k₂ f₁ f₂ M k₁≢k₂ k with k₁ ≟ k | k₂ ≟ k
  ... | yes p₁ | yes p₂ = ⊥-elim (k₁≢k₂ (trans p₁ (sym p₂)))
  ... | yes p₁ | no ¬p₂ = subst (λ α → lookup (alter k₁ f₁ (alter k₂ f₂ M)) α ≡ lookup (alter k₂ f₂ (alter k₁ f₁ M)) α) p₁ e where
                            open ≡-Reasoning
                            e = begin
                              lookup (alter k₁ f₁ (alter k₂ f₂ M)) k₁
                                ≡⟨ lookup-alter-new k₁ f₁ (alter k₂ f₂ M) ⟩
                              f₁ (lookup (alter k₂ f₂ M) k₁)
                                ≡⟨ cong f₁ (lookup-alter-old k₂ k₁ f₂ M (k₁≢k₂ ∘ sym)) ⟩
                              f₁ (lookup M k₁)
                                ≡⟨ sym (lookup-alter-new k₁ f₁ M) ⟩
                              lookup (alter k₁ f₁ M) k₁
                                ≡⟨ sym (lookup-alter-old k₂ k₁ f₂ (alter k₁ f₁ M) (k₁≢k₂ ∘ sym)) ⟩
                              lookup (alter k₂ f₂ (alter k₁ f₁ M)) k₁ ∎
  ... | no ¬p₁ | yes p₂ = subst (λ α → lookup (alter k₁ f₁ (alter k₂ f₂ M)) α ≡ lookup (alter k₂ f₂ (alter k₁ f₁ M)) α) p₂ e where
                            open ≡-Reasoning
                            e = begin
                              lookup (alter k₁ f₁ (alter k₂ f₂ M)) k₂
                                ≡⟨ lookup-alter-old k₁ k₂ f₁ (alter k₂ f₂ M) k₁≢k₂ ⟩
                              lookup (alter k₂ f₂ M) k₂
                                ≡⟨ lookup-alter-new k₂ f₂ M ⟩
                              f₂ (lookup M k₂)
                                ≡⟨ sym (cong f₂ (lookup-alter-old k₁ k₂ f₁ M k₁≢k₂)) ⟩
                              f₂ (lookup (alter k₁ f₁ M) k₂)
                                ≡⟨ sym (lookup-alter-new k₂ f₂ (alter k₁ f₁ M)) ⟩
                              lookup (alter k₂ f₂ (alter k₁ f₁ M)) k₂ ∎
  ... | no ¬p₁ | no ¬p₂ = begin
                    lookup (alter k₁ f₁ (alter k₂ f₂ M)) k
                      ≡⟨ lookup-alter-old k₁ k f₁ (alter k₂ f₂ M) ¬p₁ ⟩
                    lookup (alter k₂ f₂ M) k
                      ≡⟨ lookup-alter-old k₂ k f₂ M ¬p₂ ⟩
                    lookup M k
                      ≡⟨ sym (lookup-alter-old k₁ k f₁ M ¬p₁) ⟩
                    lookup (alter k₁ f₁ M) k
                      ≡⟨ sym (lookup-alter-old k₂ k f₂ (alter k₁ f₁ M) ¬p₂) ⟩
                    lookup (alter k₂ f₂ (alter k₁ f₁ M)) k ∎ where open ≡-Reasoning


  _∘⁺_ : {V V′ V″ : K → Set ν} (g : (k : K) → V′ k → Maybe (V″ k)) (f : (k : K) → V k → Maybe (V′ k)) → ((k : K) → V k → Maybe (V″ k))
  _∘⁺_ g f k v = f k v >>= g k

  -- basic properties of mapfilter
  mapfilter-compose : {V V′ V″ : K → Set ν}
                      (g : (k : K) → V′ k → Maybe (V″ k))
                      (f : (k : K) → V k → Maybe (V′ k)) (M : Map V) →
                      mapfilter g (mapfilter f M) ≡′ mapfilter (g ∘⁺ f) M

  private
    maybe-lemma : {A B C : Set ν} (F : A → Maybe B) (G : B → Maybe C) (x : Maybe A) → maybe′ (λ v → maybe′ G nothing (F v)) nothing x ≡ maybe′ G nothing (maybe′ F nothing x)
    maybe-lemma _ _ (just x) = refl
    maybe-lemma _ _ nothing = refl

  mapfilter-compose g f M k = begin
    lookup (mapfilter g (mapfilter f M)) k
      ≡⟨ lookup-mapfilter g (mapfilter f M) k ⟩
    maybe′ (g k) nothing (lookup (mapfilter f M) k)
      ≡⟨ cong (λ x → maybe′ (g k) nothing x) (lookup-mapfilter f M k) ⟩
    maybe′ (g k) nothing (maybe′ (f k) nothing (lookup M k))
      ≡⟨ sym (maybe-lemma (f k) (g k) (lookup M k)) ⟩
    maybe′ (λ v → maybe′ (g k) nothing (f k v)) nothing (lookup M k)
      ≡⟨ sym (lookup-mapfilter (g ∘⁺ f) M k) ⟩
    lookup (mapfilter (g ∘⁺ f) M) k ∎ where open ≡-Reasoning

  -- map
  map : {V V′ : K → Set ν} → ((k : K) → V k → V′ k) → Map V → Map V′
  map f = mapfilter (λ k v → just (f k v))

  -- filter
  filter : {V V′ : K → Set ν} → ((k : K) → V k → Bool) → Map V → Map V
  filter f = mapfilter (λ k v → if (f k v) then just v else nothing)

  -- fromList
  fromList : {V : K → Set ν} → List (Σ K V) → Map V
  fromList [] = empty
  fromList ((k₁ , v₁) ∷ kvs) = upsert k₁ v₁ (fromList kvs)

  -- unions preferring left and right
  infixr 5 _∪⁺_
  infixr 5 _⁺∪_
  _∪⁺_ : {V : K → Set ν} → Map V → Map V → Map V
  _⁺∪_ : {V : K → Set ν} → Map V → Map V → Map V
  _∪⁺_ = combine (λ k x y → maybe′ (const y) x y)
  A ⁺∪ B = B ∪⁺ A

  toList  : {V : K → Set ν} → Map V → List (Σ K V)
  toList = fold [] _∷_

