-- There are many ways of setting up the theory of limits (and there
-- would be many more if we had functor categories, which are
-- unavailable to us without passing to setoids of homomorphisms).

-- The most highbrow is to treat them as right Kan extensions along
-- projections to the terminal category. See "KanExtension" for
-- code supporting this approach.

-- A middlebrow approach, supported in this file, is the classical
-- definition in terms of "cones" (implemented as natural
-- transformations from constant functors).

-- A lowbrow approach is to give explicit definitions for particular
-- limit shapes, at the level of objects, homomorphisms and equations
-- between composites. This is done in "Limits.Pullback" and other
-- similar modules under Limits.

-- It is desirable to have good comparison results, so that one
-- can work in agreeably specific settings but call theorems that
-- have been proved in generality. We have a good set of results
-- passing between middle and low, but not yet between high and
-- middle.


module Sheffield.CategoryTheory-Set.Limits where

open import Data.Sum using (inj₁ ; inj₂)
open import Data.Unit
open import Function using (flip)
open import Level
open import Relation.Binary.PropositionalEquality

open import Sheffield.CategoryTheory-Set.Categories
open import Sheffield.CategoryTheory-Set.Categories.Diagrams using (point)
open import Sheffield.CategoryTheory-Set.Categories.Join
open import Sheffield.CategoryTheory-Set.Functors
open import Sheffield.CategoryTheory-Set.Functors.Isomorphism
open import Sheffield.CategoryTheory-Set.KanExtension
open import Sheffield.CategoryTheory-Set.Misc
open import Sheffield.CategoryTheory-Set.NaturalTransformations
open import Sheffield.CategoryTheory-Set.NaturalTransformations.Equality
open existsUnique


-- Cones can be thought of either as functors from a join category, or as natural tranformations from a constant functor

module cone-definitions-agree {ℓ₁ ℓ₂ ℓ′₁ ℓ′₂ : Level} (K : Category {ℓ₁} {ℓ′₁}) (C : Category {ℓ₂} {ℓ′₂}) where

  conesˡ : (F : Functor (point ✫ K) C) → NatTrans (constFunctor K C (Functor.obj F (inj₁ tt))) (F ⊙ in₂)
  conesˡ F = makeNatTrans component naturality where
    open ≡-Reasoning
    open Category C
    open Category (point ✫ K) hiding (id ; id-r) renaming (_•_ to _•′_) 

    F₀ = Functor.obj F
    F₁ = λ {x} {y} f → Functor.hom F {x} {y} f

    component : (x : Category.obj K) → Category.hom C (Functor.obj (constFunctor K C (Functor.obj F (inj₁ tt))) x) (Functor.obj (F ⊙ in₂) x)
    component x = Functor.hom F (j-inj₁₂ tt x)

    naturality : {x y : Category.obj K} (f : Category.hom K x y) → Category.compose C (component y) (Functor.hom (constFunctor K C (Functor.obj F (inj₁ tt))) f) ≡ Category.compose C (Functor.hom (F ⊙ in₂) f) (component x)
    naturality {x} {y} f = begin
      F₁ (j-inj₁₂ tt y) • id (F₀ (inj₁ tt))
        ≡⟨ id-r (F₁ (j-inj₁₂ tt y)) ⟩
      F₁ (j-inj₁₂ tt y)
        ≡⟨ refl ⟩
      Functor.hom F (j-inj₂ x y f •′ j-inj₁₂ tt x)
        ≡⟨ Functor.compose F (j-inj₂ x y f) (j-inj₁₂ tt x) ⟩
      Functor.hom F (j-inj₂ x y f) • Functor.hom F (j-inj₁₂ tt x) ∎

  conesʳ : (a : Category.obj C) (F : Functor K C) → NatTrans (constFunctor K C a) F → Functor (point ✫ K) C
  conesʳ a F (makeNatTrans Θ₀ Θ₁) = makeFunctor obj hom id assoc where
    F₀ = Functor.obj F

    obj : Category.obj (point ✫ K) → Category.obj C
    obj (inj₁ tt) = a
    obj (inj₂ y) = F₀ y

    hom : {x y : Category.obj (point ✫ K)} → Category.hom (point ✫ K) x y → Category.hom C (obj x) (obj y)
    hom (j-inj₁ x y f) = Category.id C a
    hom (j-inj₂ x y f) = Functor.hom F f
    hom (j-inj₁₂ x y) = Θ₀ y

    id : (x : Category.obj (point ✫ K)) → hom (Category.id (point ✫ K) x) ≡ Category.id C (obj x)
    id (inj₁ x) = refl
    id (inj₂ y) = Functor.id F y

    assoc : {x y z : Category.obj (point ✫ K)} (g : Category.hom (point ✫ K) y z) (f : Category.hom (point ✫ K) x y) → hom (Category.compose (point ✫ K) g f) ≡ Category.compose C (hom g) (hom f)
    assoc (j-inj₁ y z g) (j-inj₁ x .y f) = sym (Category.id-l C (Category.id C a))
    assoc (j-inj₂ y z g) (j-inj₂ x .y f) = Functor.compose F g f
    assoc (j-inj₂ y z g) (j-inj₁₂ x .y) = trans (sym (Category.id-r C (Θ₀ z))) (Θ₁ g)
    assoc (j-inj₁₂ y z) (j-inj₁ x .y f) = sym (Category.id-r C (Θ₀ z))

open cone-definitions-agree public



record IsLimit {ℓ₁ ℓ′₁ ℓ₂ ℓ′₂ : Level}
  {K : Category {ℓ₁} {ℓ′₁}} {C : Category {ℓ₂} {ℓ′₂}}
  (F : Functor K C) (x : Category.obj C)
  (Θ : NatTrans (constFunctor K C x) F) : Set (ℓ₁ ⊔ ℓ′₁ ⊔ ℓ₂ ⊔ ℓ′₂) where

  constructor make-Limit

  field
    factorisations : (a : Category.obj C) (Ψ : NatTrans (constFunctor K C a) F) → existsUnique (Category.hom C a x) _≡_ (λ f → Ψ ≡₂ Θ •̂ constNatTrans f)

  witnesses : (a : Category.obj C) (Ψ : NatTrans (constFunctor K C a) F) → Category.hom C a x
  witnesses a Ψ = witness (factorisations a Ψ)

  satisfactions : (a : Category.obj C) (Ψ : NatTrans (constFunctor K C a) F) → Ψ ≡₂ Θ •̂ constNatTrans (witnesses a Ψ)
  satisfactions a Ψ = satisfaction (factorisations a Ψ)

  uniquenesses : (a : Category.obj C) (Ψ : NatTrans (constFunctor K C a) F) (f : Category.hom C a x) → Ψ ≡₂ Θ •̂ constNatTrans f → f ≡ witnesses a Ψ
  uniquenesses a Ψ = uniqueness (factorisations a Ψ)

{-
  as-KanExtension : IsRightKanExtension {ℓ₁} {ℓ′₁} {zero} {zero} {ℓ₂} {ℓ′₂} (constFunctor {ℓ₁} {ℓ′₁} {zero} {zero} K point tt) F (constFunctor point C x) (Θ •̂ ≅₁-to-NatTrans (const-≅₁-l (constFunctor K point tt) x))
  as-KanExtension = make-RightKanExtension rke where
    rke : (R′ : Functor point C) (Θ′ : NatTrans (R′ ⊙ constFunctor K point tt) F) → existsUnique (NatTrans R′ (constFunctor point C x)) (_≡₂_) (λ Φ → Θ′ ≡₂ Θ •̂ ≅₁-to-NatTrans (const-≅₁-l (constFunctor K point tt) x) •̂ (Φ ⊙̂ idNatTrans (constFunctor K point tt)))
    rke R′ Θ′ = makeUnique W⁺ E⁺ U⁺ where
      open ≡-Reasoning

      W = witnesses
      E = satisfactions
      U = uniquenesses

      Θ₀ = NatTrans.component Θ
      Θ₁ : {a b : Category.obj K} (f : Category.hom K a b) → Category.compose C (Θ₀ b) (Category.id C x) ≡ Category.compose C (Functor.hom F f) (Θ₀ a)
      Θ₁ = NatTrans.naturality Θ

      P : NatTrans (constFunctor K C (Functor.obj R′ tt)) F
      P = makeNatTrans (NatTrans.component Θ′) (λ {α} {β} f → trans (cong (Category.compose C (NatTrans.component Θ′ β)) (sym (Functor.id R′ tt))) (NatTrans.naturality Θ′ f))

      W⁺ : NatTrans R′ (constFunctor point C x)
      W⁺ = makeNatTrans component naturality where
        component : (a : Category.obj point) → Category.hom C (Functor.obj R′ a) (Functor.obj (constFunctor point C x) a)
        component tt = W (Functor.obj R′ tt) P
        naturality : {α β : Category.obj point} (f : Category.hom point α β) → Category.compose C (component β) (Functor.hom R′ f) ≡ Category.compose C (Functor.hom (constFunctor point C x) f) (component α)
        naturality tt = trans (trans (cong (Category.compose C _) (Functor.id R′ tt)) (Category.id-r C _)) (sym (Category.id-l C _))

      E⁺ : Θ′ ≡₂ Θ •̂ ≅₁-to-NatTrans (const-≅₁-l (constFunctor K point tt) x) •̂ (W⁺ ⊙̂ idNatTrans (constFunctor K point tt))
      E⁺ a = begin
        NatTrans.component Θ′ a
          ≡⟨ E (Functor.obj R′ tt) P a ⟩
        Category.compose C (NatTrans.component Θ a) (W (Functor.obj R′ tt) (makeNatTrans (NatTrans.component Θ′) (λ {α} {β} f → trans (cong (Category.compose C (NatTrans.component Θ′ β)) (sym (Functor.id R′ tt))) (NatTrans.naturality Θ′ f))))
          ≡⟨ cong (Category.compose C (NatTrans.component Θ a)) (sym (Category.id-r C _)) ⟩
        Category.compose C (NatTrans.component Θ a) (Category.compose C (W (Functor.obj R′ tt) (makeNatTrans (NatTrans.component Θ′) (λ {α} {β} f → trans (cong (Category.compose C (NatTrans.component Θ′ β)) (sym (Functor.id R′ tt))) (NatTrans.naturality Θ′ f)))) (Category.id C (Functor.obj R′ tt)))
          ≡⟨ cong (λ α → Category.compose C (NatTrans.component Θ a) (Category.compose C (W (Functor.obj R′ tt) (makeNatTrans (NatTrans.component Θ′) (λ {α} {β} f → trans (cong (Category.compose C (NatTrans.component Θ′ β)) (sym (Functor.id R′ tt)))  (NatTrans.naturality Θ′ f)))) α)) (sym (Functor.id R′ tt)) ⟩
        Category.compose C (NatTrans.component Θ a) (Category.compose C (W (Functor.obj R′ tt) (makeNatTrans (NatTrans.component Θ′) (λ {α} {β} f → trans (cong (Category.compose C (NatTrans.component Θ′ β)) (sym (Functor.id R′ tt))) (NatTrans.naturality Θ′ f)))) (Functor.hom R′ tt))
          ≡⟨ cong (flip (Category.compose C) _) (sym (Category.id-r C (NatTrans.component Θ a))) ⟩
        Category.compose C (Category.compose C (NatTrans.component Θ a) (Category.id C x)) (Category.compose C (W (Functor.obj R′ tt) (makeNatTrans (NatTrans.component Θ′) (λ {α} {β} f → trans (cong (Category.compose C (NatTrans.component Θ′ β)) (sym (Functor.id R′ tt))) (NatTrans.naturality Θ′ f)))) (Functor.hom R′ tt)) ∎

      U⁺ : (W′ : NatTrans R′ (constFunctor point C x)) → Θ′ ≡₂ Θ •̂ ≅₁-to-NatTrans (const-≅₁-l (constFunctor K point tt) x) •̂ (W′ ⊙̂ idNatTrans (constFunctor K point tt)) → W′ ≡₂ W⁺
      U⁺ W′ e tt = U (Functor.obj R′ tt) P (NatTrans.component W′ tt) e′ where
        e′ : (z : Category.obj K) → NatTrans.component Θ′ z ≡ Category.compose C (NatTrans.component Θ z) (NatTrans.component W′ tt)
        e′ z = begin
          NatTrans.component Θ′ z
            ≡⟨ e z ⟩
          Category.compose C (Category.compose C (NatTrans.component Θ z) (Category.id C x)) (Category.compose C (NatTrans.component W′ tt) (Functor.hom R′ tt))
            ≡⟨ cong (λ α → Category.compose C α (Category.compose C (NatTrans.component W′ tt) (Functor.hom R′ tt))) (Category.id-r C (NatTrans.component Θ z)) ⟩
          Category.compose C (NatTrans.component Θ z) (Category.compose C (NatTrans.component W′ tt) (Functor.hom R′ tt))
            ≡⟨ cong (λ α → Category.compose C (NatTrans.component Θ z) (Category.compose C (NatTrans.component W′ tt) α)) (Functor.id R′ tt) ⟩
          Category.compose C (NatTrans.component Θ z) (Category.compose C (NatTrans.component W′ tt) (Category.id C (Functor.obj R′ tt)))
            ≡⟨ cong (Category.compose C (NatTrans.component Θ z)) (Category.id-r C _) ⟩
          Category.compose C (NatTrans.component Θ z) (NatTrans.component W′ tt) ∎
-}


module kan-extension-vs-limit {ℓ₁ ℓ′₁ ℓ₂ ℓ′₂ : Level}
  {K : Category {ℓ₁} {ℓ′₁}} {C : Category {ℓ₂} {ℓ′₂}}
  (F : Functor K C) (x : Category.obj C)
  (Θ : NatTrans (constFunctor K C x) F)
  (rke : IsRightKanExtension (constFunctor K point tt) F (constFunctor point C x) (Θ •̂ ≅₁-to-NatTrans (const-≅₁-l (constFunctor K point tt) x))) where

  open IsRightKanExtension rke

{-
  as-Limit : IsLimit F x Θ
  as-Limit = make-Limit lim where
    lim : (a : Category.obj C) (Ψ : NatTrans (constFunctor K C a) F) → existsUnique (Category.hom C a x) _≡_ (λ f → Ψ ≡₂ Θ •̂ constNatTrans f)
    lim a Ψ = makeUnique W E U where
      W : Category.hom C a x
      W = {!witnesses (constFunctor point C a) Ψ!}

      E : (x' : Category.obj K) → NatTrans.component Ψ x' ≡ NatTrans.component (Θ •̂ constNatTrans W) x'
      E = {!!}

      U : (a' : Category.hom C a x) → Ψ ≡₂ Θ •̂ constNatTrans a' → a' ≡ W
      U = {!!}
-}
open kan-extension-vs-limit public

