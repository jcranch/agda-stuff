module Sheffield.SimplicialSets.Simplicial.Categorical where

-- Δ is the full subcategory of Cat on the simplex categories

open import Data.Fin
open import Data.Nat hiding (_≤_ ; _⊔_)
open import Function
open import Function.Equality hiding (id ; _∘_)
open import Level hiding (zero ; suc)
open import Relation.Binary.PropositionalEquality as PropEq

open import Sheffield.CategoryTheory-Setoid.Categories
open import Sheffield.CategoryTheory-Setoid.Categories.Equivalence
open import Sheffield.CategoryTheory-Setoid.Examples.Categories
open import Sheffield.CategoryTheory-Setoid.Examples.Simplex
open import Sheffield.CategoryTheory-Setoid.Functors
open import Sheffield.CategoryTheory-Setoid.Functors.Isomorphism
open import Sheffield.CategoryTheory-Setoid.Functors.Isomorphism.Properties using (≅₁-obj)
open import Sheffield.CategoryTheory-Setoid.NaturalTransformations
open import Sheffield.CategoryTheory-Setoid.NaturalTransformations.Equality
open import Sheffield.CategoryTheory-Setoid.SetoidFunction

open import Sheffield.SimplicialSets.Simplicial



Δ′ : Category {Level.zero} {Level.zero} {Level.zero}
Δ′ = full-subcategory Categories simplex

delta-as-categories : Δ ≅₀ Δ′
delta-as-categories = equivalent₀ R L U C where

  -- doubtless these functions, or similar, are hidden somewhere in the standard library

  ≤≥→≡-Fin : {n : ℕ} (i j : Fin n) → i ≤ j → j ≤ i → i ≡ j
  ≤≥→≡-Fin zero zero i≤j j≤i = refl
  ≤≥→≡-Fin zero (suc j) _ ()
  ≤≥→≡-Fin (suc i) zero () _
  ≤≥→≡-Fin (suc i) (suc j) (s≤s i≤j) (s≤s j≤i) = PropEq.cong suc (≤≥→≡-Fin i j i≤j j≤i)

  simplex-iso : {n : ℕ} (i j : Fin n) → Iso._≅_ (simplex n) i j → i ≡ j
  simplex-iso i j (Iso.make-≅ f (Iso.makeIso f⁻¹ _ _)) = ≤≥→≡-Fin i j f f⁻¹

  ≡→≤-ℕ : {x y : ℕ} → x ≡ y → Data.Nat._≤_ x y
  ≡→≤-ℕ {zero} refl = z≤n
  ≡→≤-ℕ {suc n} refl = s≤s (≡→≤-ℕ {n} refl)

  ≤-refl : {x : ℕ} → Data.Nat._≤_ x x
  ≤-refl = ≡→≤-ℕ refl

  ≡→≤-Fin : {n : ℕ} {i j : Fin n} → i ≡ j → i ≤ j
  ≡→≤-Fin {n} {i} {j} e = ≡→≤-ℕ (PropEq.cong toℕ e)

  R : Functor Δ Δ′
  R = makeFunctor id hom fid fcompose where

    homset : {x y : ℕ} → Category.homset Δ x y → Category.homset Δ′ x y
    homset (ordered-maps.ord map isOrdered) = record {
      obj = map ;
      hom = λ {i} {j} → record {
        _⟨$⟩_ = isOrdered i j;
        cong = id } ;
      id = λ _ → tt ;
      compose = λ _ _ → tt }

    hom-cong : {x y : ℕ} {f g : ordered-maps.Ordered x y} (e : (i : _) → _) → homset f ≅₁ homset g
    hom-cong {x} {y} {f} {g} e = isomorphic₁ Φ Ψ u c where
      Φ : NatTrans (homset f) (homset g)
      Φ = makeNatTrans (λ x → ≡→≤-Fin (e x)) (λ _ → tt)
      Ψ : NatTrans (homset g) (homset f)
      Ψ = makeNatTrans (λ x → ≡→≤-Fin (PropEq.sym (e x))) (λ _ → tt)
      u : _ ≈₂ _
      u = make-≈₂ (λ _ → tt)
      c : _ ≈₂ _
      c = make-≈₂ (λ _ → tt)

    hom : {x y : ℕ} → Category.hom Δ x y ⟶ Category.hom Δ′ x y
    hom {x} {y} = record {
      _⟨$⟩_ = homset;
      cong = hom-cong }

    fid : (x : ℕ) → homset (Category.id Δ x) ≅₁ Category.id Δ′ x
    fid x = isomorphic₁ Φ Ψ u c where
      Φ : NatTrans (homset (Category.id Δ x)) (Category.id Δ′ x)
      Φ = makeNatTrans (λ i → ≤-refl) (λ _ → tt)
      Ψ : NatTrans (Category.id Δ′ x) (homset (Category.id Δ x))
      Ψ = makeNatTrans (λ i → ≤-refl) (λ _ → tt)
      u : _ ≈₂ _
      u = make-≈₂ (λ _ → tt)
      c : _ ≈₂ _
      c = make-≈₂ (λ _ → tt)

    fcompose : {x y z : ℕ} (G : Category.homset Δ y z) (F : Category.homset Δ x y) → homset (Category._•_ Δ G F) ≅₁ Category._•_ Δ′ (homset G) (homset F)
    fcompose (ordered-maps.ord g g₀) (ordered-maps.ord f f₀) = isomorphic₁ Φ Ψ u c where
      G = ordered-maps.ord g g₀
      F = ordered-maps.ord f f₀
      Φ : NatTrans (homset (Category._•_ Δ G F)) (Category._•_ Δ′ (homset G) (homset F))
      Φ = makeNatTrans (λ _ → ≤-refl) (λ _ → tt)
      Ψ : NatTrans (Category._•_ Δ′ (homset G) (homset F)) (homset (Category._•_ Δ G F))
      Ψ = makeNatTrans (λ _ → ≤-refl) (λ _ → tt)
      u : _ ≈₂ _
      u = make-≈₂ (λ _ → tt)
      c : _ ≈₂ _
      c = make-≈₂ (λ _ → tt)

  L : Functor Δ′ Δ
  L = makeFunctor id hom (λ _ _ → refl) (λ _ _ _ → refl) where

    homset : {x y : ℕ} → Category.homset Δ′ x y → Category.homset Δ x y
    homset {x} {y} F = ordered-maps.ord (Functor.obj F) (λ i j → Functor.homsets F)

    hom : {x y : ℕ} → Category.hom Δ′ x y ⟶ Category.hom Δ x y
    hom {x} {y} = record {
      _⟨$⟩_ = homset ;
      cong = λ {F} {G} F≅₁G i → simplex-iso _ _ (≅₁-obj F≅₁G i) }

  U : L ⊙ R ≅₁ idFunctor Δ
  U = isomorphic₁ Φ Ψ (make-≈₂ (λ _ _ → refl)) (make-≈₂ (λ _ _ → refl)) where
    Φ : NatTrans (L ⊙ R) (idFunctor Δ)
    Φ = makeNatTrans (λ n → ordered-maps.id) (λ _ _ → refl)
    Ψ : NatTrans (idFunctor Δ) (L ⊙ R)
    Ψ = makeNatTrans (λ n → ordered-maps.id) (λ _ _ → refl)

  C : R ⊙ L ≅₁ idFunctor Δ′
  C = isomorphic₁ Φ Ψ u c where
    Φ : NatTrans (R ⊙ L) (idFunctor Δ′)
    Φ = makeNatTrans F I where
      F : (n : ℕ) → Functor _ _
      F n = record {
        obj = id ;
        hom = record {
          _⟨$⟩_ = id ;
          cong = λ _ → tt } ;
        id = λ _ → tt ;
        compose = λ _ _ → tt }
      I : {m n : ℕ} (f : Category.homset Δ′ m n) → _ ≅₁ _
      I f = isomorphic₁ Ξ Ω (make-≈₂ (λ _ → tt)) (make-≈₂ (λ _ → tt)) where
        Ξ = makeNatTrans (λ _ → ≤-refl) (λ _ → tt)
        Ω = makeNatTrans (λ _ → ≤-refl) (λ _ → tt)
    Ψ : NatTrans (idFunctor Δ′) (R ⊙ L)
    Ψ = makeNatTrans G J where
      G : (n : ℕ) → Functor _ _
      G n = record {
        obj = id ;
        hom = record {
          _⟨$⟩_ = id ;
          cong = λ _ → tt } ;
        id = λ _ → tt ;
        compose = λ _ _ → tt }
      J : {m n : ℕ} (f : Category.homset Δ′ m n) → _ ≅₁ _
      J f = isomorphic₁ Υ Λ (make-≈₂ (λ _ → tt)) (make-≈₂ (λ _ → tt)) where
        Υ = makeNatTrans (λ _ → ≤-refl) (λ _ → tt)
        Λ = makeNatTrans (λ _ → ≤-refl) (λ _ → tt)
    u : Ψ •̂ Φ ≈₂ idNatTrans (R ⊙ L)
    u = make-≈₂ I′ where
      I′ : (n : ℕ) → _ ≅₁ _
      I′ n = isomorphic₁ א ב (make-≈₂ (λ _ → tt)) (make-≈₂ (λ _ → tt)) where
        א = makeNatTrans (λ _ → ≤-refl) (λ _ → tt)
        ב = makeNatTrans (λ _ → ≤-refl) (λ _ → tt)
    c : Φ •̂ Ψ ≈₂ idNatTrans (idFunctor Δ′)
    c = make-≈₂ J′ where
      J′ : (n : ℕ) → _ ≅₁ _
      J′ n = isomorphic₁ ג ד (make-≈₂ (λ _ → tt)) (make-≈₂ (λ _ → tt)) where
        ג = makeNatTrans (λ _ → ≤-refl) (λ _ → tt)
        ד = makeNatTrans (λ _ → ≤-refl) (λ _ → tt)


Δ→Cat : Functor Δ Categories
Δ→Cat = full-subcategory-inclusion Categories simplex ⊙ _≅₀_.obverse delta-as-categories