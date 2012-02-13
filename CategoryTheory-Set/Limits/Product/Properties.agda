-- We prove that products are unital and commutative. Associativity would be nice, but it would be best to have a highbrow approach.


module Limits.Product.Properties where

open import Data.Product
open import Function hiding (id)
open import Level
open import Relation.Binary.PropositionalEquality

open import Categories
open import Limits.Product
open import Limits.Terminal
open import Misc


module with-fixed-category {ℓ ℓ′ : Level} (C : Category {ℓ} {ℓ′}) where
  open Category C

  product-unital-l : (t : obj) (term : IsTerminal C t) (x : obj) → IsProduct-lowbrow C t x x (exists-to-1 C t term x) (id x)
  product-unital-l t term x = make-product (λ f₁ f₂ → makeUnique f₂ ( trans (unique-to-1 C t term _) (sym (unique-to-1 C t term _)) ,′ id-l f₂ ) (λ a r → trans (sym (id-l a)) (proj₂ r)))
  product-unital-r : (t : obj) (term : IsTerminal C t) (x : obj) → IsProduct-lowbrow C x t x (id x) (exists-to-1 C t term x)
  product-unital-r t term x = make-product (λ f₁ f₂ → makeUnique f₁ (id-l f₁ ,′ trans (unique-to-1 C t term _) (sym (unique-to-1 C t term _))) (λ a r → trans (sym (id-l a)) (proj₁ r)))

  product-commutative : {x y x×y : obj} {p₁ : hom x×y x} {p₂ : hom x×y y} → IsProduct-lowbrow C x y x×y p₁ p₂ → IsProduct-lowbrow C y x x×y p₂ p₁
  product-commutative (make-product φ) = make-product (λ f₂ f₁ → makeUnique (existsUnique.witness (φ f₁ f₂)) (swap (existsUnique.satisfaction (φ f₁ f₂))) (λ a r → existsUnique.uniqueness (φ f₁ f₂) a (swap r)))

  product-functorial : {x y x×y : obj} {p₁ : hom x×y x} {p₂ : hom x×y y} {x′ y′ x′×y′ : obj} {p′₁ : hom x′×y′ x′} {p′₂ : hom x′×y′ y′} (f : hom x x′) (g : hom y y′) → IsProduct-lowbrow C x y x×y p₁ p₂ → IsProduct-lowbrow C x′ y′ x′×y′ p′₁ p′₂ → hom x×y x′×y′
  product-functorial {p₁ = p₁} {p₂ = p₂} f g (make-product φ) (make-product φ′) = existsUnique.witness (φ′ (f • p₁) (g • p₂))

open with-fixed-category public