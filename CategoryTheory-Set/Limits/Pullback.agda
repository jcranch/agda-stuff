module Limits.Pullback where

open import Data.Product renaming (proj₁ to pr₁ ; proj₂ to pr₂)
open import Data.Sum
open import Data.Unit
open import Level
open import Relation.Binary.PropositionalEquality
open ≡-Reasoning

open import Limits
open import Categories
open import Categories.Diagrams
open import Categories.Join
open import Categories.Join.Properties
open import Functors
open import Misc
open import NaturalTransformations
open import NaturalTransformations.Equality



module pullback-context {ℓ₁ ℓ′₁ : Level} (C : Category {ℓ₁} {ℓ′₁})
  {a b c d : Category.obj C} (f₁ : Category.hom C b d) (f₂ : Category.hom C c d)
  (p₁ : Category.hom C a b) (p₂ : Category.hom C a c)
  (eq : Category.compose C f₁ p₁ ≡ Category.compose C f₂ p₂) where

  open Category C

  private
    f₁₂ : Functor ↗↖ C
    f₁₂ = ↗↖-functor f₁ f₂
    Θ : NatTrans (constFunctor ↗↖ C a) f₁₂
    Θ = ↗↖-nat-trans (constFunctor ↗↖ C a) f₁₂ p₁ p₂ (f₁ • p₁) (id-r _) (trans (id-r _) eq)

  IsPullback : Set (ℓ₁ ⊔ ℓ′₁)
  IsPullback = IsLimit f₁₂ a Θ


  data IsPullback-lowbrow : Set (ℓ₁ ⊔ ℓ′₁) where
    make-pullback : (φ : {x : obj} (q₁ : hom x b) (q₂ : hom x c) → (f₁ • q₁ ≡ f₂ • q₂) → existsUnique (hom x a) _≡_ (λ h → (p₁ • h ≡ q₁) × (p₂ • h ≡ q₂))) → IsPullback-lowbrow


  pullback↑ : IsPullback-lowbrow → IsPullback
  pullback↑ (make-pullback φ) = make-Limit H where
    H : (e : obj) (Ψ : NatTrans (constFunctor ↗↖ C e) f₁₂) → existsUnique (hom e a) _≡_ (λ f → Ψ ≡₂ (Θ •̂ constNatTrans f))
    H e Ψ = makeUnique p s u where
      Ψ₀ = NatTrans.component Ψ
      o = (φ (Ψ₀ (inj₁ (inj₁ tt))) (Ψ₀ (inj₁ (inj₂ tt))) (trans (sym (NatTrans.naturality Ψ (j-inj₁₂ (inj₁ tt) tt))) (NatTrans.naturality Ψ (j-inj₁₂ (inj₂ tt) tt))))
      p = existsUnique.witness o
      s : (x : Category.obj ↗↖) → Ψ₀ x ≡ NatTrans.component (Θ •̂ constNatTrans p) x
      s (inj₁ (inj₁ tt)) = sym (pr₁ (existsUnique.satisfaction o))
      s (inj₁ (inj₂ tt)) = sym (pr₂ (existsUnique.satisfaction o))
      s (inj₂ tt) = begin
        Ψ₀ (inj₂ tt)
          ≡⟨ sym (id-r _) ⟩
        Ψ₀ (inj₂ tt) • id e
          ≡⟨ NatTrans.naturality Ψ (j-inj₁₂ (inj₁ tt) tt) ⟩
        f₁ • Ψ₀ (inj₁ (inj₁ tt))
          ≡⟨ cong (compose f₁) (sym (pr₁ (existsUnique.satisfaction o))) ⟩
        f₁ • (p₁ • existsUnique.witness o)
          ≡⟨ assoc _ _ _ ⟩
        (f₁ • p₁) • existsUnique.witness o ∎
      u : (g : hom e a) → Ψ ≡₂ Θ •̂ constNatTrans g → g ≡ p
      u g E = existsUnique.uniqueness o g (sym (E (inj₁ (inj₁ tt))) ,′ sym (E (inj₁ (inj₂ tt))))


  pullback↓ : IsPullback → IsPullback-lowbrow
  pullback↓ (make-Limit factorisations) = make-pullback K where
    K : {x : obj} (q₁ : hom x b) (q₂ : hom x c) → f₁ • q₁ ≡ f₂ • q₂ → existsUnique (hom x a) _≡_ (λ h → p₁ • h ≡ q₁ × p₂ • h ≡ q₂)
    K {x} q₁ q₂ i = makeUnique p (s₁ ,′ s₂) u where
      o = factorisations x (↗↖-nat-trans (constFunctor ↗↖ C x) (↗↖-functor f₁ f₂) q₁ q₂ (f₁ • q₁) (id-r _) (trans (id-r _) i))
      p : hom x a
      p = existsUnique.witness o
      s₁ : p₁ • p ≡ q₁
      s₁ = sym (existsUnique.satisfaction o (inj₁ (inj₁ tt)))
      s₂ : p₂ • p ≡ q₂
      s₂ = sym (existsUnique.satisfaction o (inj₁ (inj₂ tt)))
      u : (g : hom x a) → p₁ • g ≡ q₁ × p₂ • g ≡ q₂ → g ≡ p
      u g I = existsUnique.uniqueness o g R where
        R : (z : (⊤ ⊎ ⊤) ⊎ ⊤) → _
        R (inj₁ (inj₁ tt)) = sym (pr₁ I)
        R (inj₁ (inj₂ tt)) = sym (pr₂ I)
        R (inj₂ tt) = begin
          f₁ • q₁ 
            ≡⟨ cong (compose f₁) (sym (pr₁ I)) ⟩
          f₁ • (p₁ • g)
            ≡⟨ assoc _ _ _ ⟩
          (f₁ • p₁) • g ∎

open pullback-context public

IsPushout : {ℓ₁ ℓ′₁ : Level} (C : Category {ℓ₁} {ℓ′₁}) {a b c d : Category.obj C} (f₁ : Category.hom C d b) (f₂ : Category.hom C d c) (p₁ : Category.hom C b a) (p₂ : Category.hom C c a) (eq : Category.compose C p₁ f₁ ≡ Category.compose C p₂ f₂) → Set (ℓ₁ ⊔ ℓ′₁)
IsPushout C = IsPullback (opposite C)



record Pullback {ℓ₁ ℓ′₁ : Level} (C : Category {ℓ₁} {ℓ′₁}) {b c d : Category.obj C} (f₁ : Category.hom C b d) (f₂ : Category.hom C c d) : Set (ℓ₁ ⊔ ℓ′₁) where
  field
    _×̣_ : Category.obj C
    proj₁ : Category.hom C _×̣_ b
    proj₂ : Category.hom C _×̣_ c
    equation : Category.compose C f₁ proj₁ ≡ Category.compose C f₂ proj₂
    isPullback : IsPullback-lowbrow C f₁ f₂ proj₁ proj₂ equation

Pushout : {ℓ₁ ℓ′₁ : Level} (C : Category {ℓ₁} {ℓ′₁}) {b c d : Category.obj C} (f₁ : Category.hom C d b) (f₂ : Category.hom C d b) → Set (ℓ₁ ⊔ ℓ′₁)
Pushout C = Pullback (opposite C)



HasPullbacks : {ℓ₁ ℓ′₁ : Level} (C : Category {ℓ₁} {ℓ′₁}) → Set (ℓ₁ ⊔ ℓ′₁)
HasPullbacks C = {b c d : Category.obj C} (f₁ : Category.hom C b d) (f₂ : Category.hom C c d) → Pullback C f₁ f₂

HasPushouts : {ℓ₁ ℓ′₁ : Level} (C : Category {ℓ₁} {ℓ′₁}) → Set (ℓ₁ ⊔ ℓ′₁)
HasPushouts C = HasPullbacks (opposite C)
