module Sheffield.CategoryTheory-Set.Limits.Equaliser where

open import Data.Sum
open import Data.Unit
open import Level
open import Relation.Binary.PropositionalEquality

open import Sheffield.CategoryTheory-Set.Limits
open import Sheffield.CategoryTheory-Set.Categories
open import Sheffield.CategoryTheory-Set.Categories.Diagrams
open import Sheffield.CategoryTheory-Set.Categories.Join
open import Sheffield.CategoryTheory-Set.Categories.Join.Properties
open import Sheffield.CategoryTheory-Set.Categories.Parallel
open import Sheffield.CategoryTheory-Set.Functors
open import Sheffield.CategoryTheory-Set.Misc
open import Sheffield.CategoryTheory-Set.NaturalTransformations
open import Sheffield.CategoryTheory-Set.NaturalTransformations.Equality
open ≡-Reasoning


module equaliser-context {ℓ₁ ℓ′₁ : Level} (C : Category {ℓ₁} {ℓ′₁})
  {s t e : Category.obj C} (f₁ f₂ : Category.hom C s t) (k : Category.hom C e s)
  (eq : Category.compose C f₁ k ≡ Category.compose C f₂ k) where

  open Category C


  IsEqualiser : Set (ℓ₁ ⊔ ℓ′₁)
  IsEqualiser = IsLimit F e Θ where
    F : Functor ⇉ C
    F = (⇉-functor f₁ f₂)
    Θ : NatTrans (constFunctor ⇉ C e) F
    Θ = ⇉-nat-trans (constFunctor ⇉ C e) F k (f₁ • k) (id-r (f₁ • k)) (trans (id-r (f₁ • k)) eq)



  data IsEqualiser-lowbrow : Set (ℓ₁ ⊔ ℓ′₁) where
    make-equaliser : (φ : {a : obj} (g : hom a s) → f₁ • g ≡ f₂ • g → existsUnique (hom a e) _≡_ (λ h → k • h ≡ g)) → IsEqualiser-lowbrow



  equaliser↑ : IsEqualiser-lowbrow → IsEqualiser
  equaliser↑ (make-equaliser E) = make-Limit F where
    F : (a : obj) (Ψ : NatTrans _ _) → existsUnique _ _ _
    F a Ψ = makeUnique witness satisfaction uniqueness where
      Θ = ⇉-nat-trans (constFunctor ⇉ C e) (⇉-functor f₁ f₂) k (Category.compose C f₁ k) (id-r _) (trans (id-r _) eq)
      p = E (NatTrans.component Ψ source) (trans (sym (NatTrans.naturality Ψ (parallel-map (inj₁ tt)))) (NatTrans.naturality Ψ (parallel-map (inj₂ tt))))
      witness = existsUnique.witness p
      satisfaction : Ψ ≡₂ Θ •̂ constNatTrans witness
      satisfaction source = sym (existsUnique.satisfaction p)
      satisfaction target = begin
        NatTrans.component Ψ target
          ≡⟨ sym (id-r _) ⟩
        NatTrans.component Ψ target • id a
          ≡⟨ NatTrans.naturality Ψ (parallel-map (inj₁ tt)) ⟩
        f₁ • NatTrans.component Ψ source
          ≡⟨ cong (Category.compose C f₁) (sym (existsUnique.satisfaction p)) ⟩
        f₁ • (k • (existsUnique.witness (E (NatTrans.component Ψ source) (trans (sym (NatTrans.naturality Ψ (parallel-map (inj₁ tt)))) (NatTrans.naturality Ψ (parallel-map (inj₂ tt)))))))
          ≡⟨ assoc _ _ _ ⟩
        (f₁ • k) • (existsUnique.witness (E (NatTrans.component Ψ source) (trans (sym (NatTrans.naturality Ψ (parallel-map (inj₁ tt)))) (NatTrans.naturality Ψ (parallel-map (inj₂ tt)))))) ∎
      uniqueness : (g : hom a e) → Ψ ≡₂ Θ •̂ constNatTrans g → g ≡ witness
      uniqueness g c = existsUnique.uniqueness p g (sym (c source))



  equaliser↓ : IsEqualiser → IsEqualiser-lowbrow
  equaliser↓ (make-Limit F) = make-equaliser E where
    E : {a : obj} (g : hom a s) → _ ≡ _ → existsUnique _ _ _
    E {a} g eq = makeUnique w c u where
      p = F a (⇉-nat-trans (constFunctor ⇉ C a) (⇉-functor f₁ f₂) g (f₁ • g) (id-r _) (trans (id-r _) eq))
      w = existsUnique.witness p
      c = sym (existsUnique.satisfaction p source)
      u : (h : hom a e) → k • h ≡ g → h ≡ w
      u h i = existsUnique.uniqueness p h d where
        d : (x : Category.obj ⇉) → _
        d source = sym i
        d target = trans (cong (Category.compose C f₁) (sym i)) (assoc _ _ _)
    
open equaliser-context public

IsCoequaliser : {ℓ₁ ℓ′₁ : Level} (C : Category {ℓ₁} {ℓ′₁}) {s t e : Category.obj C} (f₁ f₂ : Category.hom C s t) (k : Category.hom C t e) → Category.compose C k f₁ ≡ Category.compose C k f₂ → Set (ℓ₁ ⊔ ℓ′₁)
IsCoequaliser C f₁ f₂ k e = IsEqualiser (opposite C) f₁ f₂ k e



record Equaliser {ℓ₁ ℓ′₁ : Level} (C : Category {ℓ₁} {ℓ′₁}) {s t : Category.obj C} (f₁ f₂ : Category.hom C s t) : Set (ℓ₁ ⊔ ℓ′₁) where
  field
    limit : Category.obj C
    kernel : Category.hom C limit s
    equation : Category.compose C f₁ kernel ≡ Category.compose C f₂ kernel
    isEqualiser : IsEqualiser-lowbrow C f₁ f₂ kernel equation

Coequaliser : {ℓ₁ ℓ′₁ : Level} (C : Category {ℓ₁} {ℓ′₁}) {s t : Category.obj C} (f₁ f₂ : Category.hom C s t) → Set (ℓ₁ ⊔ ℓ′₁)
Coequaliser C = Equaliser (opposite C)



HasEqualisers : {ℓ₁ ℓ′₁ : Level} (C : Category {ℓ₁} {ℓ′₁}) → Set (ℓ₁ ⊔ ℓ′₁)
HasEqualisers C = {s t : Category.obj C} (f₁ f₂ : Category.hom C s t) → Equaliser C f₁ f₂

HasCoequalisers : {ℓ₁ ℓ′₁ : Level} (C : Category {ℓ₁} {ℓ′₁}) → Set (ℓ₁ ⊔ ℓ′₁)
HasCoequalisers C = HasEqualisers (opposite C)