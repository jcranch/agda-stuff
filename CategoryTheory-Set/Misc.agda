module Misc where

open import Level
open import Relation.Binary.PropositionalEquality as PropEq using (_≡_ ; refl)

cong₃ : ∀ {a b c d} {A : Set a} {B : Set b} {C : Set c} {D : Set d} (f : A → B → C → D) {x y u v p q} → x ≡ y → u ≡ v → p ≡ q → f x u p ≡ f y v q
cong₃ f refl refl refl = refl


