module KanExtension.Properties where

open import Level
open import Relation.Binary
open import Relation.Binary.PropositionalEquality

open import Categories
open import Categories.Comma
open import Functors
open import Functors.Composition
open import Functors.Properties
open import KanExtension
open import Misc
open import NaturalTransformations
open import NaturalTransformations.Equality

open existsUnique


-- to do:
--   uniqueness results?
--   use "make-RightKanExtension" in the identity and composition
--   Kan extensions really are extensions for fully faithful functors?
--   modularise the identity and composition
--   get everything working :-p



right-kan-equation : {ℓ₁ ℓ′₁ ℓ₂ ℓ′₂ ℓ₃ ℓ′₃ : Level}
  {C : Category {ℓ₁} {ℓ′₁}} {D : Category {ℓ₂} {ℓ′₂}} {S : Category {ℓ₃} {ℓ′₃}}
  {F : Functor C D} {X : Functor C S} {R : Functor D S}
  {Θ : NatTrans (R ⊙ F) X} (K : IsRightKanExtension F X R Θ) →
  (R′ : Functor D S) (Θ′ : NatTrans (R′ ⊙ F) X) (x : Category.obj C) →
  NatTrans.component Θ′ x ≡ Category.compose S (NatTrans.component Θ x) (NatTrans.component (IsRightKanExtension.witnesses K R′ Θ′) (Functor.obj F x))
right-kan-equation {_} {_} {_} {_} {_} {_} {C} {D} {S} {F} {X} {R} {Θ} K R′ Θ′ x = e where
  open ≡-Reasoning
  open Category S
  open IsRightKanExtension K
  id-D = Category.id D
  F₀ = Functor.obj F
  R′₀ = Functor.obj R′
  R′₁ = λ {x} {y} f → Functor.hom R′ {x} {y} f
  Θ₀ = NatTrans.component Θ
  Θ′₀ = NatTrans.component Θ′
  e = begin
    Θ′₀ x
      ≡⟨ satisfactions R′ Θ′ x ⟩
    Θ₀ x • (NatTrans.component (witnesses R′ Θ′) (F₀ x) • R′₁ (id-D (F₀ x)))
      ≡⟨ assoc _ _ _ ⟩
    Θ₀ x • NatTrans.component (witnesses R′ Θ′) (F₀ x) • R′₁ (id-D (F₀ x))
      ≡⟨ cong (λ α → Θ₀ x • NatTrans.component (witnesses R′ Θ′) (F₀ x) • α) (Functor.id R′ (F₀ x)) ⟩
    Θ₀ x • NatTrans.component (witnesses R′ Θ′) (F₀ x) • id (R′₀ (F₀ x))
      ≡⟨ id-r _ ⟩
    Θ₀ x • NatTrans.component (witnesses R′ Θ′) (F₀ x) ∎

{-
-- Kan extension along identity functors doesn't change a functor
right-kan-identity : {ℓ₁ ℓ′₁ ℓ₂ ℓ′₂ : Level}
  {C : Category {ℓ₁} {ℓ′₁}} {S : Category {ℓ₂} {ℓ′₂}}
  (X : Functor C S) → IsRightKanExtension (idFunctor C) X X (⊙-unitor-r X)
right-kan-identity {C = C} {S = S} X = make-RightKanExtension Ran where
  Ran : _ → _ → _
  Ran R Θ = makeUnique P Ξ ∃ ! where
    open ≡-Reasoning
    open Category S

    objC = Category.obj C
    idC = Category.id C

    X₀ = Functor.obj X
    R₀ = Functor.obj R

    R₁ = λ {x} {y} f → Functor.hom R {x} {y} f

    Θ₀ = NatTrans.component Θ

    P : NatTrans R X → Set _
    P Φ = Θ ≡₂ ⊙-unitor-r X •̂ (Φ ⊙̂ idNatTrans (idFunctor C))

    P-lemma : (Φ : NatTrans R X) → P Φ → (x : objC) → NatTrans.component Θ x ≡ NatTrans.component Φ x
    P-lemma Φ E x = begin
      Θ₀ x
        ≡⟨ E x ⟩
      id (X₀ x) • (Φ₀ x • R₁ (idC x))
        ≡⟨ id-l (Φ₀ x • R₁ (idC x)) ⟩
      Φ₀ x • R₁ (idC x)
        ≡⟨ cong (λ α → Φ₀ x • α) (Functor.id R x) ⟩
      Φ₀ x • id (R₀ x)
        ≡⟨ id-r (Φ₀ x) ⟩
      Φ₀ x ∎ where Φ₀ = NatTrans.component Φ

    Ξ = makeNatTrans (NatTrans.component Θ) (NatTrans.naturality Θ)

    ∃ : (x : objC) → Θ₀ x ≡ id (X₀ x) • (Θ₀ x • R₁ (idC x))
    ∃ x = begin
      Θ₀ x
        ≡⟨ sym (id-r (Θ₀ x)) ⟩
      Θ₀ x • id (R₀ x)
        ≡⟨ cong (λ α → Θ₀ x • α) (sym (Functor.id R x)) ⟩
      Θ₀ x • R₁ (idC x)
        ≡⟨ sym (id-l (Θ₀ x • R₁ (idC x))) ⟩
      id (X₀ x) • (Θ₀ x • R₁ (idC x)) ∎

    ! : (Ξ′ : NatTrans R X) → P Ξ′ → Ξ′ ≡₂ Ξ
    ! Ξ′ p x = sym (P-lemma Ξ′ p x)
-}

-- The Kan extension of a composite is an iterated Kan extension
{-
right-kan-composition : {ℓ₁ ℓ′₁ ℓ₂ ℓ′₂ ℓ₃ ℓ′₃ ℓ₄ ℓ′₄ : Level}
  {C : Category {ℓ₁} {ℓ′₁}} {D : Category {ℓ₂} {ℓ′₂}} {E : Category {ℓ₃} {ℓ′₃}}
  {S : Category {ℓ₄} {ℓ′₄}}
  (F : Functor C D) (G : Functor D E)
  (X₁ : Functor C S) (X₂ : Functor D S) (X₃ : Functor E S)
  (Θ₁₂ : NatTrans (X₂ ⊙ F) X₁) (Θ₂₃ : NatTrans (X₃ ⊙ G) X₂) →
  IsRightKanExtension F X₁ X₂ Θ₁₂ → IsRightKanExtension G X₂ X₃ Θ₂₃ → IsRightKanExtension (G ⊙ F) X₁ X₃ (Θ₁₂ •̂ (Θ₂₃ ⊙̂ idNatTrans F) •̂ ⊙-associator X₃ G F)
right-kan-composition {D = D} {E = E} {S = S} F G X₁ X₂ X₃ Θ₁₂ Θ₂₃ K K′ = make-RightKanExtension Ran where
  Ran : _ → _ → _
  Ran R Θ = makeUnique P Ξ ∃ ! where
    open Category S

    θ = NatTrans.component Θ
    θ₁₂ = NatTrans.component Θ₁₂
    θ₂₃ = NatTrans.component Θ₂₃

    F₀ = Functor.obj F
    G₀ = Functor.obj G
    R₀ = Functor.obj R
    X₃₀ = Functor.obj X₃

    id-D = Category.id D
    id-E = Category.id E

    G₁ = λ {x} {y} f → Functor.hom G {x} {y} f
    X₃₁ = λ {x} {y} f → Functor.hom X₃ {x} {y} f
    R₁ = λ {x} {y} f → Functor.hom R {x} {y} f

    P = λ Φ → Θ ≡₂ Θ₁₂ •̂ (Θ₂₃ ⊙̂ idNatTrans F) •̂ ⊙-associator X₃ G F •̂ (Φ ⊙̂ idNatTrans (G ⊙ F))

    Υ : NatTrans (R ⊙ G) X₂
    Υ = IsRightKanExtension.witnesses K (R ⊙ G) (Θ •̂ ⊙-associator⁻¹ R G F)
    Υ₀ = NatTrans.component Υ

    Ξ : NatTrans R X₃
    Ξ = IsRightKanExtension.witnesses K′ R Υ
    Ξ₀ = NatTrans.component Ξ

    ∃ : Θ ≡₂ Θ₁₂ •̂ (Θ₂₃ ⊙̂ idNatTrans F) •̂ ⊙-associator X₃ G F •̂ (Ξ ⊙̂ idNatTrans (G ⊙ F))
    ∃ x = begin
      θ x
        ≡⟨ right-kan-equation {Θ = Θ₁₂} K (R ⊙ G) (Θ •̂ ⊙-associator⁻¹ R G F) x ⟩
      θ₁₂ x • Υ₀ (F₀ x)
        ≡⟨ cong (λ α → θ₁₂ x • α) (right-kan-equation {Θ = Θ₂₃} K′ R Υ (F₀ x)) ⟩
      θ₁₂ x • (θ₂₃ (F₀ x) • Ξ₀ (G₀ (F₀ x)))
        ≡⟨ assoc (θ₁₂ x) (θ₂₃ (F₀ x)) (Ξ₀ (G₀ (F₀ x))) ⟩
      θ₁₂ x • θ₂₃ (F₀ x) • Ξ₀ (G₀ (F₀ x))
        ≡⟨ cong (λ α → θ₁₂ x • α • Ξ₀ (G₀ (F₀ x))) (sym (id-r (θ₂₃ (F₀ x)))) ⟩
      θ₁₂ x • (θ₂₃ (F₀ x) • id (X₃₀ (G₀ (F₀ x)))) • Ξ₀ (G₀ (F₀ x))
        ≡⟨ cong (λ α → θ₁₂ x • (θ₂₃ (F₀ x) • α) • Ξ₀ (G₀ (F₀ x))) (sym (Functor.id X₃ _)) ⟩
      θ₁₂ x • (θ₂₃ (F₀ x) • X₃₁ (id-E (G₀ (F₀ x)))) • Ξ₀ (G₀ (F₀ x))
        ≡⟨ cong (λ α → θ₁₂ x • (θ₂₃ (F₀ x) • X₃₁ α) • Ξ₀ (G₀ (F₀ x))) (sym (Functor.id G _)) ⟩
      θ₁₂ x • (θ₂₃ (F₀ x) • X₃₁ (G₁ (id-D (F₀ x)))) • Ξ₀ (G₀ (F₀ x))
        ≡⟨ cong (λ α → θ₁₂ x • (θ₂₃ (F₀ x) • X₃₁ (G₁ (id-D (F₀ x)))) • α) (sym (id-r (Ξ₀ (G₀ (F₀ x))))) ⟩
      θ₁₂ x • (θ₂₃ (F₀ x) • X₃₁ (G₁ (id-D (F₀ x)))) • (Ξ₀ (G₀ (F₀ x)) • id (R₀ (G₀ (F₀ x))))
        ≡⟨ cong (λ α → _ • (_ • α)) (sym (Functor.id R _)) ⟩
      θ₁₂ x • (θ₂₃ (F₀ x) • X₃₁ (G₁ (id-D (F₀ x)))) • (Ξ₀ (G₀ (F₀ x)) • R₁ (id-E (G₀ (F₀ x))))
        ≡⟨ cong (λ α → _) (sym (id-r _)) ⟩
      θ₁₂ x • (θ₂₃ (F₀ x) • X₃₁ (G₁ (id-D (F₀ x)))) • id (X₃₀ (G₀ (F₀ x))) • (Ξ₀ (G₀ (F₀ x)) • R₁ (id-E (G₀ (F₀ x)))) ∎ where open ≡-Reasoning

    module uniqueness (Ξ′ : NatTrans R X₃) (E : P Ξ′) where
      -- should follow by employing uniqueness for the kan extension along F
      !′ : Ξ′ ⊙̂ (idNatTrans G) ≡₂ Ξ ⊙̂ (idNatTrans G)
      !′ x = {!!}

      -- should follow by employing uniqueness for the kan extension along G, together with !
      ! : Ξ′ ≡₂ Ξ
      ! x = {!!}
    open uniqueness using (!)
-}

{-
module 2-categorical-naturality {ℓ₁ ℓ′₁ ℓ₂ ℓ′₂ ℓ₃ ℓ′₃ ℓ₄ ℓ′₄ : Level}
  {C : Category {ℓ₁} {ℓ′₁}} {D : Category {ℓ₂} {ℓ′₂}} {E : Category {ℓ₃} {ℓ′₃}}
  {S : Category {ℓ₄} {ℓ′₄}}
  (F : Functor C D) (G : Functor E D)
  (X : Functor C S) (X′ : Functor D S)
  (Θ : NatTrans (X′ ⊙ F) X) 
  (K : IsRightKanExtension F X X′ Θ) where
  
  private
    Y = X ⊙ Proj₂ G F
    Y′ = X′ ⊙ G
    Ψ : NatTrans ((X′ ⊙ G) ⊙ Proj₁ G F) (X ⊙ Proj₂ G F)
    Ψ = ((Θ ⊙̂ idNatTrans (Proj₂ G F))) •̂ ⊙-associator X′ F (Proj₂ G F) •̂ (idNatTrans X′ ⊙̂ Proj₁₂ G F) •̂ ⊙-associator⁻¹ X′ G (Proj₁ G F)

    W : (R′ : Functor E S) → NatTrans (R′ ⊙ Proj₁ G F) Y → NatTrans R′ Y′
    W R′ Θ′ = {!!}

    ∃ : (R′ : Functor E S) (Θ′ : NatTrans (R′ ⊙ Proj₁ G F) Y) → Θ′ ≡₂ Ψ •̂ (W R′ Θ′ ⊙̂ idNatTrans (Proj₁ G F))
    ∃ R′ Θ′ = {!!}

    U : (R′ : Functor E S) (Θ′ : NatTrans (R′ ⊙ Proj₁ G F) Y) (W′ : NatTrans R′ Y′) → Θ′ ≡₂ Ψ •̂ (W′ ⊙̂ idNatTrans (Proj₁ G F)) → W′ ≡₂ W R′ Θ′
    U R′ Θ′ = {!!}

  right-kan-pullback : IsRightKanExtension (Proj₁ G F) Y Y′ Ψ
  right-kan-pullback = make-RightKanExtension (Proj₁ G F) Y Y′ Ψ W ∃ U

open 2-categorical-naturality public
-}