{-# OPTIONS --guarded #-}
module Examples.Bool where

open import Prelude

open import LaterG

private variable
  ℓ ℓ′ ℓ″ : Level
  A : 𝒰 ℓ
  B : 𝒰 ℓ′
  C : 𝒰 ℓ″

-- bools as codata

record Bool : 𝒰 (ℓsuc ℓ) where
  no-eta-equality ; pattern
  constructor mkBool
  field
    If : {A : 𝒰 ℓ} → A → A → A

True : Bool {ℓ}
True = mkBool λ t f → t

False : Bool {ℓ}
False = mkBool λ t f → f
