module Sheffield.Data.Nat.Primality where

open import Data.Nat
open import Data.Nat.Primality

prime≥1 : {p : ℕ} → (Prime p) → (1 ≤ p)
prime≥1 {zero} ()
prime≥1 {suc zero} ()
prime≥1 {suc (suc n)} _ = (s≤s z≤n)

prime≥2 : {p : ℕ} → (Prime p) → (2 ≤ p)
prime≥2 {zero} ()
prime≥2 {suc zero} ()
prime≥2 {suc (suc n)} _ = s≤s (s≤s z≤n)
