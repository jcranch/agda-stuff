-- Adjunctions, including two abortive attempts at defining their composition.


module Sheffield.CategoryTheory-Setoid.Adjunctions where

open import Level
open import Relation.Binary

open import Sheffield.CategoryTheory-Setoid.Categories
open import Sheffield.CategoryTheory-Setoid.Functors
open import Sheffield.CategoryTheory-Setoid.Functors.Composition
open import Sheffield.CategoryTheory-Setoid.NaturalTransformations
open import Sheffield.CategoryTheory-Setoid.NaturalTransformations.Equality



module adjunction-theory {ℓ₁ ℓ′₁ ℓ″₁ ℓ₂ ℓ′₂ ℓ″₂ : Level}
  {C : Category {ℓ₁} {ℓ′₁} {ℓ″₁}} {D : Category {ℓ₂} {ℓ′₂} {ℓ″₂}}
  (F : Functor D C) (G : Functor C D) where

  private
    F₀ = Functor.obj F
    G₀ = Functor.obj G
    F₁ = λ {x} {y} → Functor.homsets F {x} {y}
    G₁ = λ {x} {y} → Functor.homsets G {x} {y}

  -- we spend some time now producing "on morphisms" versions of the adjunction
  -- equations, which is certainly boring but saves having to manipulate lengthy
  -- sequences of identity morphisms when we come to do things with it.

  module ε-η-theory (ε : NatTrans (F ⊙ G) (idFunctor C)) (η : NatTrans (idFunctor D) (G ⊙ F)) where
    ε₀ = NatTrans.component ε
    η₀ = NatTrans.component η
    module ε-η-theory-1 where
      open Category C hiding (obj)
      open Category D using (obj)
                             
      eq-εη-lhs : (x : obj) → id (F₀ x) • ((ε₀ (F₀ x) • F₁ (G₁ (id (F₀ x)))) • (id (F₀ (G₀ (F₀ x))) • ((id (F₀ (G₀ (F₀ x))) • F₁ (η₀ x)) • id (F₀ x)))) ≈ ε₀ (F₀ x) • F₁ (η₀ x)
      eq-εη-lhs x = begin
        id (F₀ x) • ((ε₀ (F₀ x) • F₁ (G₁ (id (F₀ x)))) • (id (F₀ (G₀ (F₀ x))) • ((id (F₀ (G₀ (F₀ x))) • F₁ (η₀ x)) • id (F₀ x))))
          ≈⟨ id-l _ ⟩
        (ε₀ (F₀ x) • F₁ (G₁ (id (F₀ x)))) • (id (F₀ (G₀ (F₀ x))) • ((id (F₀ (G₀ (F₀ x))) • F₁ (η₀ x)) • id (F₀ x)))
          ≈⟨ •-cong (•-cong ≈-refl (Functor.hom-cong F (Functor.id G _))) (id-l _) ⟩
        (ε₀ (F₀ x) • F₁ (Category.id D (G₀ (F₀ x)))) • ((id (F₀ (G₀ (F₀ x))) • F₁ (η₀ x)) • id (F₀ x))
          ≈⟨ •-cong (•-cong ≈-refl (Functor.id F _)) (id-r _) ⟩
        (ε₀ (F₀ x) • id (F₀ (G₀ (F₀ x)))) • (id (F₀ (G₀ (F₀ x))) • F₁ (η₀ x))
          ≈⟨ •-cong (id-r _) (id-l _) ⟩
        ε₀ (F₀ x) • F₁ (η₀ x) ∎ where open ≈-Reasoning _ _
    open ε-η-theory-1 public

    module ε-η-theory-2 where
      open Category D hiding (obj)
      open Category C using (obj)

      eq-ηε-lhs : (x : obj) → id (G₀ x) • ((id (G₀ x) • G₁ (ε₀ x)) • (id (G₀ (F₀ (G₀ x))) • ((η₀ (G₀ x) • id (G₀ x)) • id (G₀ x)))) ≈ G₁ (ε₀ x) • η₀ (G₀ x)
      eq-ηε-lhs x = begin
        id (G₀ x) • ((id (G₀ x) • G₁ (ε₀ x)) • (id (G₀ (F₀ (G₀ x))) • ((η₀ (G₀ x) • id (G₀ x)) • id (G₀ x))))
          ≈⟨ id-l _ ⟩
        (id (G₀ x) • G₁ (ε₀ x)) • (id (G₀ (F₀ (G₀ x))) • ((η₀ (G₀ x) • id (G₀ x)) • id (G₀ x)))
          ≈⟨ •-cong (id-l _) (id-l _) ⟩
        G₁ (ε₀ x) • ((η₀ (G₀ x) • id (G₀ x)) • id (G₀ x))
          ≈⟨ •-cong ≈-refl (id-r _) ⟩
        G₁ (ε₀ x) • (η₀ (G₀ x) • id (G₀ x))
          ≈⟨ •-cong ≈-refl (id-r _) ⟩
        G₁ (ε₀ x) • η₀ (G₀ x) ∎ where open ≈-Reasoning _ _
    open ε-η-theory-2 public


  record Adjunction : Set (ℓ₁ ⊔ ℓ′₁ ⊔ ℓ″₁ ⊔ ℓ₂ ⊔ ℓ′₂ ⊔ ℓ″₂) where
    constructor make-Adj

    field
      ε : NatTrans (F ⊙ G) (idFunctor C)
      η : NatTrans (idFunctor D) (G ⊙ F)

      eq-εη : ⊙-unitor-l F •̂ (ε ⊙̂ idNatTrans F) •̂ ⊙-associator⁻¹ F G F •̂ (idNatTrans F ⊙̂ η) •̂ ⊙-unitor-r⁻¹ F ≈₂ idNatTrans F
      eq-ηε : ⊙-unitor-r G •̂ (idNatTrans G ⊙̂ ε) •̂ ⊙-associator G F G •̂ (η ⊙̂ idNatTrans G) •̂ ⊙-unitor-l⁻¹ G ≈₂ idNatTrans G

    open ε-η-theory ε η

    module eq-εη-lowbrow where
      open Category C hiding (obj)
      open Category D using (obj)

      eq-εη′ : (x : obj) → ε₀ (F₀ x) • F₁ (η₀ x) ≈ id (F₀ x)
      eq-εη′ x = ≈-trans (≈-sym (eq-εη-lhs x)) (_≈₂_.component-≈ eq-εη x)
    open eq-εη-lowbrow public

    module eq-ηε-lowbrow where
      open Category D hiding (obj)
      open Category C using (obj)

      eq-ηε′ : (x : obj) → G₁ (ε₀ x) • η₀ (G₀ x) ≈ id (G₀ x)
      eq-ηε′ x = ≈-trans (≈-sym (eq-ηε-lhs x)) (_≈₂_.component-≈ eq-ηε x)
    open eq-ηε-lowbrow public

  _⊣_ : Set (ℓ₁ ⊔ ℓ′₁ ⊔ ℓ″₁ ⊔ ℓ₂ ⊔ ℓ′₂ ⊔ ℓ″₂)
  _⊣_ = Adjunction


  -- if you want you can build an adjunction using only the lowbrow versions of
  -- the equations
  module ε-η-theory-revisited (ε : NatTrans (F ⊙ G) (idFunctor C)) (η : NatTrans (idFunctor D) (G ⊙ F)) where
    open ε-η-theory ε η

    open Category C
    open Category D renaming (obj to obj′ ; _•_ to _•′_ ; _≈_ to _≈′_ ; id to id′ ; ≈-trans to ≈′-trans)

    make-adjunction : (φ : (x : obj′) → ε₀ (F₀ x) • F₁ (η₀ x) ≈ id (F₀ x))
      (ψ : (x : obj) → G₁ (ε₀ x) •′ η₀ (G₀ x) ≈′ id′ (G₀ x)) → Adjunction
    make-adjunction φ ψ = record {
      ε = ε ;
      η = η ; 
      eq-εη = make-≈₂ (λ x → ≈-trans (eq-εη-lhs x) (φ x)) ;
      eq-ηε = make-≈₂ (λ x → ≈′-trans (eq-ηε-lhs x) (ψ x)) }

  open ε-η-theory-revisited public

open adjunction-theory public



module adjunction-composition-theory-highbrow {ℓ₁ ℓ′₁ ℓ″₁ ℓ₂ ℓ′₂ ℓ″₂ ℓ₃ ℓ′₃ ℓ″₃ : Level}
  {C : Category {ℓ₁} {ℓ′₁} {ℓ″₁}}
  {D : Category {ℓ₂} {ℓ′₂} {ℓ″₂}}
  {E : Category {ℓ₃} {ℓ′₃} {ℓ″₃}}
  {F : Functor D C} {G : Functor C D}
  {F′ : Functor E D} {G′ : Functor D E}
  (A : F ⊣ G)
  (A′ : F′ ⊣ G′) where

  open Adjunction F G A
  open Adjunction F′ G′ A′ renaming (ε to ε′ ; η to  η′ ; eq-εη to eq-εη′ ; eq-ηε to eq-ηε′)

  compose-adjunctions : (F ⊙ F′) ⊣ (G′ ⊙ G)

  compose-adjunctions = make-Adj ε⁺ η⁺ {!!} {!!} where -- the bored reader may
-- while away some time by invoking ctrl-C ctrl-comma on either of these holes.
    ε⁺ = ε •̂ (idNatTrans F ⊙̂ (⊙-unitor-l G •̂ (ε′ ⊙̂ idNatTrans G) •̂ ⊙-associator⁻¹ F′ G′ G)) •̂ ⊙-associator F F′ (G′ ⊙ G)
    η⁺ = ⊙-associator⁻¹ G′ G (F ⊙ F′) •̂ (idNatTrans G′ ⊙̂ (⊙-associator G F F′ •̂ (η ⊙̂ idNatTrans F′) •̂ ⊙-unitor-l⁻¹ F′)) •̂ η′


module adjunction-composition-theory-lowbrow {ℓ₁ ℓ′₁ ℓ″₁ ℓ₂ ℓ′₂ ℓ″₂ ℓ₃ ℓ′₃ ℓ″₃ : Level}
  {C : Category {ℓ₁} {ℓ′₁} {ℓ″₁}}
  {D : Category {ℓ₂} {ℓ′₂} {ℓ″₂}}
  {E : Category {ℓ₃} {ℓ′₃} {ℓ″₃}}
  {F : Functor D C} {G : Functor C D}
  {F′ : Functor E D} {G′ : Functor D E}
  (F⊣G : F ⊣ G) (F′⊣G′ : F′ ⊣ G′) where

  open Adjunction F G F⊣G hiding (eq-εη ; eq-ηε) renaming (eq-εη′ to eq-εη ; eq-ηε′ to eq-ηε)
  open Adjunction F′ G′ F′⊣G′ hiding (eq-εη ; eq-ηε) renaming (ε to ε′ ; η to η′)

  open Category C
  open Category D renaming (obj to obj′ ; _•_ to _•′_ ; _≈_ to _≈′_ ; id to id′ ; ≈-trans to ≈′-trans ; module ≈-Reasoning to ≈′-Reasoning ; •-cong to •′-cong ; ≈-refl to ≈′-refl ; id-l to id-l′ ; id-r to id-r′)
  open Category E renaming (obj to obj″ ; _•_ to _•″_ ; _≈_ to _≈″_ ; id to id″ ; ≈-trans to ≈″-trans ; module ≈-Reasoning to ≈″-Reasoning ; •-cong to •″-cong ; ≈-refl to ≈″-refl ; id-l to id-l″ ; id-r to id-r″)

  private
    ε⁺ = ε •̂ (idNatTrans F ⊙̂ (⊙-unitor-l G •̂ (ε′ ⊙̂ idNatTrans G) •̂ ⊙-associator⁻¹ F′ G′ G)) •̂ ⊙-associator F F′ (G′ ⊙ G)
    η⁺ = ⊙-associator⁻¹ G′ G (F ⊙ F′) •̂ (idNatTrans G′ ⊙̂ (⊙-associator G F F′ •̂ (η ⊙̂ idNatTrans F′) •̂ ⊙-unitor-l⁻¹ F′)) •̂ η′

    F₀ = Functor.obj F
    G₀ = Functor.obj G
    F₁ = λ {x} {y} → Functor.homsets F {x} {y}
    G₁ = λ {x} {y} → Functor.homsets G {x} {y}
    F′₀ = Functor.obj F′
    G′₀ = Functor.obj G′
    F′₁ = λ {x} {y} → Functor.homsets F′ {x} {y}
    G′₁ = λ {x} {y} → Functor.homsets G′ {x} {y}

    ε₀ = NatTrans.component ε
    η₀ = NatTrans.component η
    ε′₀ = NatTrans.component ε′
    η′₀ = NatTrans.component η′
    ε⁺₀ = NatTrans.component ε⁺
    η⁺₀ = NatTrans.component η⁺

    ε⁺₀-simplify : (x : obj) → ε⁺₀ x ≈ ε₀ x • F₁ (ε′₀ (G₀ x))
    ε⁺₀-simplify x = begin
      ε₀ x • ((id (F₀ (G₀ x)) • F₁ (id′ (G₀ x) •′ ((ε′₀ (G₀ x) •′ F′₁ (G′₁ (id′ (G₀ x)))) •′ id′ (F′₀ (G′₀ (G₀ x)))))) • id (F₀ (F′₀ (G′₀ (G₀ x)))))
        ≈⟨ •-cong ≈-refl (id-r _) ⟩
      ε₀ x • (id (F₀ (G₀ x)) • F₁ (id′ (G₀ x) •′ ((ε′₀ (G₀ x) •′ F′₁ (G′₁ (id′ (G₀ x)))) •′ id′ (F′₀ (G′₀ (G₀ x))))))
        ≈⟨ •-cong ≈-refl (id-l _) ⟩
      ε₀ x • F₁ (id′ (G₀ x) •′ ((ε′₀ (G₀ x) •′ F′₁ (G′₁ (id′ (G₀ x)))) •′ id′ (F′₀ (G′₀ (G₀ x)))))
        ≈⟨ •-cong ≈-refl (Functor.hom-cong F (id-l′ _)) ⟩
      ε₀ x • F₁ ((ε′₀ (G₀ x) •′ F′₁ (G′₁ (id′ (G₀ x)))) •′ id′ (F′₀ (G′₀ (G₀ x))))
        ≈⟨ •-cong ≈-refl (Functor.hom-cong F (id-r′ _)) ⟩
      ε₀ x • F₁ (ε′₀ (G₀ x) •′ F′₁ (G′₁ (id′ (G₀ x))))
        ≈⟨ •-cong ≈-refl (Functor.hom-cong F (•′-cong ≈′-refl (Functor.hom-cong F′ (Functor.id G′ _)))) ⟩
      ε₀ x • F₁ (ε′₀ (G₀ x) •′ F′₁ (id″ (G′₀ (G₀ x))))
        ≈⟨ •-cong ≈-refl (Functor.hom-cong F (•′-cong ≈′-refl (Functor.id F′ _))) ⟩
      ε₀ x • F₁ (ε′₀ (G₀ x) •′ id′ (F′₀ (G′₀ (G₀ x))))
        ≈⟨ •-cong ≈-refl (Functor.hom-cong F (id-r′ _)) ⟩
      ε₀ x • F₁ (ε′₀ (G₀ x)) ∎ where open ≈-Reasoning _ _


    η⁺₀-simplify : (x : obj″) → η⁺₀ x ≈″ G′₁ (η₀ (F′₀ x)) •″ η′₀ x
    η⁺₀-simplify x = begin
      {!!}
        ≈⟨ {!!} ⟩
      G′₁ (η₀ (F′₀ x)) •″ η′₀ x ∎ where open ≈″-Reasoning _ _

{-
    η⁺₀-simplify : (x : obj″) → η⁺₀ x ≈″ G′₁ (η₀ (F′₀ x)) •″ η′₀ x
    η⁺₀-simplify x = begin
      (id″ (G′₀ (G₀ (F₀ (F′₀ x)))) •″ (id″ (G′₀ (G₀ (F₀ (F′₀ x)))) •″ (G′₁ ((id′ (G₀ (F₀ (F′₀ x))) •′ (η₀ (F′₀ x) •′ id′ (F′₀ x))) •′ id′ (F′₀ x))))) •″ η′₀ x
        ≈⟨ •″-cong (id-l″ _) ≈″-refl ⟩
      (id″ (G′₀ (G₀ (F₀ (F′₀ x)))) •″ (G′₁ ((id′ (G₀ (F₀ (F′₀ x))) •′ (η₀ (F′₀ x) •′ id′ (F′₀ x))) •′ id′ (F′₀ x)))) •″ η′₀ x
        ≈⟨ •″-cong (id-l″ _) ≈″-refl ⟩
      (G′₁ ((id′ (G₀ (F₀ (F′₀ x))) •′ (η₀ (F′₀ x) •′ id′ (F′₀ x))) •′ id′ (F′₀ x))) •″ η′₀ x
        ≈⟨ •″-cong (Functor.hom-cong G′ (id-r′ _)) ≈″-refl ⟩
      (G′₁ (id′ (G₀ (F₀ (F′₀ x))) •′ (η₀ (F′₀ x) •′ id′ (F′₀ x)))) •″ η′₀ x
        ≈⟨ •″-cong (Functor.hom-cong G′ (id-l′ _)) ≈″-refl ⟩
      (G′₁ (η₀ (F′₀ x) •′ id′ (F′₀ x))) •″ η′₀ x
        ≈⟨ •″-cong (Functor.hom-cong G′ (id-r′ _)) ≈″-refl ⟩
      G′₁ (η₀ (F′₀ x)) •″ η′₀ x ∎ where open ≈″-Reasoning _ _

  compose-adjunctions : (F ⊙ F′) ⊣ (G′ ⊙ G)

  compose-adjunctions = make-adjunction (F ⊙ F′) (G′ ⊙ G) ε⁺ η⁺ eq-εη⁺ eq-ηε⁺ where
    eq-εη⁺ : (x : obj″) → ε⁺₀ (F₀ (F′₀ x)) • F₁ (F′₁ (η⁺₀ x)) ≈ id (F₀ (F′₀ x))
    eq-εη⁺ x = begin
      ε⁺₀ (F₀ (F′₀ x)) • F₁ (F′₁ (η⁺₀ x))
        ≈⟨ •-cong (ε⁺₀-simplify _) (Functor.hom-cong F (Functor.hom-cong F′ (η⁺₀-simplify _))) ⟩
      (ε₀ (F₀ (F′₀ x)) • F₁ (ε′₀ (G₀ (F₀ (F′₀ x))))) • F₁ (F′₁ (G′₁ (η₀ (F′₀ x)) •″ η′₀ x))
        ≈⟨ {!!} ⟩ -- this is a pain when slogging away; have to remember the right
-- trick to interchange the natural transformations (namely, you employ naturality
-- of one transformation, when applied to a morphism which involves a component of
-- the other). This is all encoded more pleasantly by the interchange law.
      id (F₀ (F′₀ x)) ∎ where open ≈-Reasoning _ _

    eq-ηε⁺ : (x : obj) → G′₁ (G₁ (ε⁺₀ x)) •″ η⁺₀ (G′₀ (G₀ x)) ≈″ id″ (G′₀ (G₀ x))
    eq-ηε⁺ x = begin
      G′₁ (G₁ (ε⁺₀ x)) •″ η⁺₀ (G′₀ (G₀ x))
        ≈⟨ •″-cong (Functor.hom-cong G′ (Functor.hom-cong G (ε⁺₀-simplify _))) (η⁺₀-simplify _) ⟩
      G′₁ (G₁ (ε₀ x • F₁ (ε′₀ (G₀ x)))) •″ (G′₁ (η₀ (F′₀ (G′₀ (G₀ x)))) •″ η′₀ (G′₀ (G₀ x)))
        ≈⟨ {!!} ⟩ -- likewise!
      id″ (G′₀ (G₀ x)) ∎ where open ≈″-Reasoning _ _


-}