{-# OPTIONS --guarded #-}
module Examples.GameTree where

open import Prelude
open import Data.Bool
open import Data.Nat
open import Data.Maybe
open import Data.List

open import LaterG

private variable
  ℓ ℓ′ ℓ″ : Level
  A : 𝒰 ℓ
  B : 𝒰 ℓ′
  C : 𝒰 ℓ″

-- rose tree
record Tree (A : 𝒰 ℓ) : 𝒰 ℓ where
  inductive ; no-eta-equality ; pattern
  constructor mkTree
  field
    nd  : A
    ch▹ : List (▹ Tree A)

open Tree

mapʳ-body : (A → B) → ▹ (Tree A → Tree B) → Tree A → Tree B
mapʳ-body f m▹ t = mkTree (f (t .nd)) (map (m▹ ⊛_) (t .ch▹))

mapʳ : (A → B) → Tree A → Tree B
mapʳ f = fix (mapʳ-body f)

data Board : 𝒰 where

moves : Board → List Board
moves = {!!}

gametree-body : ▹ (Board → Tree Board) → Board → Tree Board
gametree-body g▹ b = mkTree b (map (λ x → g▹ ⊛ next x) (moves b))

gametree : Board → Tree Board
gametree = fix gametree-body

-- remove subtrees of a certain depth
prune : ℕ → Tree A → Tree A
prune  zero   t = mkTree (t .nd) []
prune (suc n) t = mkTree (t .nd) (map (prune n ⍉_) (t .ch▹))

score : Board → Board × ℕ
score = {!!}

-- Returns a Maybe Board because there is no next move in a final gamestate
maximize : Tree (Board × ℕ) → Maybe Board
maximize = {!!}

evaluate : Board → Maybe Board
evaluate = maximize ∘ mapʳ score ∘ prune 6 ∘ gametree
