{-# OPTIONS --guarded #-}
module Examples.SetIface where

open import Prelude
open import Data.Bool
open import Data.Dec
open import Data.Nat
open import Data.Nat.Two
open import Data.List

open import LaterG
open import Guarded.Partial

private variable
  ℓ ℓ′ ℓ″ : Level
  A : 𝒰 ℓ
  B : 𝒰 ℓ′
  C : 𝒰 ℓ″

foldrP : (A → B → Part B) → B → List A → Part B
foldrP _ x []       = now x
foldrP f x (a ∷ as) = f a =<<ᵖ foldrP f x as

record SetF (S▹ : ▹ 𝒰) : 𝒰 where
  inductive ; no-eta-equality ; pattern
  constructor mkSet
  field
    emp? : Bool
    has? : ℕ → Bool
    ins  : ℕ → ▸ S▹
    uni  : ▸ S▹ → Part (SetF S▹)

open SetF

Setℕ : 𝒰
Setℕ = fix SetF

-- un/rolling

⇉▹S : ▸ dfix SetF → ▹ Setℕ
⇉▹S = transport λ i → ▹[ α ] pfix SetF i α

▹S⇉ : ▹ Setℕ → ▸ dfix SetF
▹S⇉ = transport λ i → ▹[ α ] pfix SetF (~ i) α

S⇉ : Setℕ → SetF (next Setℕ)
S⇉ s =
  mkSet
    (s .emp?)
    (s .has?)
    (transport (λ i → ℕ → ▹[ α ] pfix SetF i α) (s .ins))
    (transport (λ i → ▹[ α ] (pfix SetF i α) → Part (SetF (λ α → pfix SetF i α))) (s .uni))

⇉S : SetF (next Setℕ) → Setℕ
⇉S s =
  mkSet
    (s .emp?)
    (s .has?)
    (transport (λ i → ℕ → ▹[ α ] pfix SetF (~ i) α) (s .ins))
    (transport (λ i → ▹[ α ] (pfix SetF (~ i) α) → Part (SetF (λ α → pfix SetF (~ i) α))) (s .uni))

-- ops

finiteSet-body : ▹ (List ℕ → Setℕ) → List ℕ → Setℕ
finiteSet-body f▹ l =
  ⇉S $ mkSet
    (empty? l)
    (λ n → elem (λ x y → ⌊ x ≟ y ⌋) n l)
    (λ n → f▹ ⊛ next (n ∷ l))
    (λ x▹ → later ((λ x → foldrP (λ n z → later ((now ∘ S⇉) ⍉ (z .ins n))) (S⇉ x) l) ⍉ x▹))

finiteSet : List ℕ → Setℕ
finiteSet = fix finiteSet-body

emptySet : Setℕ
emptySet = finiteSet []

evensUnion-body : ▹ (Setℕ → Setℕ) → Setℕ → Setℕ
evensUnion-body e▹ s =
  ⇉S $ mkSet
    false
    (λ n → even n or s .has? n)
    (λ n → e▹ ⊛ ⇉▹S (s .ins n))
    (λ x▹ → later ((λ f → mapᵖ (S⇉ ∘ f) (s .uni (▹S⇉ x▹))) ⍉ e▹))

evensUnion : Setℕ → Setℕ
evensUnion = fix evensUnion-body

evenSet : Setℕ
evenSet = evensUnion emptySet
