{-# OPTIONS --guarded #-}
module Examples.IOObj where

open import Prelude
open import Data.Maybe

open import LaterG
--open import Guarded.Partial

record IOTree : 𝒰 (ℓsuc 0ℓ) where
  field
    Command : 𝒰
    Response : Command → 𝒰

open IOTree

data IOProg (I : IOTree) (A : 𝒰) : 𝒰 where
  ret : (a : A) → IOProg I A
  bnd : (c : Command I) (f : Response I c → ▹ IOProg I A) → IOProg I A

_>>=ᵢ_ : ∀ {A B : 𝒰} {I : IOTree}
      → IOProg I A → (A → IOProg I B) → IOProg I B
_>>=ᵢ_ {A} {B} {I} m f =
  fix {A = IOProg I A → IOProg I B}
      (λ cih▹ → λ where
          (ret a) → f a
          (bnd c f) → bnd c λ x → cih▹ ⊛ f x)
    m

record Interface : 𝒰 (ℓsuc 0ℓ) where
  field
    Method : 𝒰
    Result : Method → 𝒰

open Interface

record Obj (I : Interface) : 𝒰 where
  inductive
  field
    mth′ : (m : Method I) → Result I m × ▹ Obj I

record IOObj (Io : IOTree) (I : Interface) : 𝒰 where
  inductive
  field
    mth : (m : Method I) → IOProg Io (Result I m × ▹ IOObj Io I)

open IOObj

-- example

data ConsoleCommand : 𝒰 where
  getLine : ConsoleCommand
  putStrLn : String → ConsoleCommand

ConsoleResponse : ConsoleCommand → 𝒰
ConsoleResponse  getLine     = Maybe String
ConsoleResponse (putStrLn _) = ⊤

ConsoleInterface : IOTree
ConsoleInterface .Command = ConsoleCommand
ConsoleInterface .Response = ConsoleResponse

cat : IOProg ConsoleInterface ⊤
cat = fix λ c▹ →
  bnd getLine
    λ where
       nothing → next (ret tt)
       (just l) → next (bnd (putStrLn l) λ _ → c▹)

data CellMethod A : 𝒰 where
  get : CellMethod A
  put : A → CellMethod A

CellResult : ∀ {A} → CellMethod A → 𝒰
CellResult {A} get     = A
CellResult     (put _) = ⊤

CellI : 𝒰 → Interface
CellI A .Method = CellMethod A
CellI A .Result = CellResult

CellC : 𝒰
CellC = IOObj ConsoleInterface (CellI String)

simpleCell : String → CellC
simpleCell = fix λ c▹ s →
  record { mth =
    λ where
       get     → bnd (putStrLn ("getting (" ++ₛ s ++ₛ ")"))
                    λ _ → next (ret (s , (c▹ ⊛ next s)))

       (put x) → bnd ((putStrLn ("putting (" ++ₛ x ++ₛ ")")))
                    λ _ → next (ret (tt , (c▹ ⊛ next x)))
  }

{-
simpleProg : IOProg ConsoleInterface ⊤
simpleProg = fix λ s▹ →
  let c₁ = simpleCell "Start" in
  bnd getLine λ where
    nothing → next (ret tt)
    (just s) → next (c₁ .mth (put s) >>=ᵢ
                      λ where
                          (_ , c₂▹) → (let qq = (λ c → c .mth get) ⍉ c₂▹ in {!!}) >>=ᵢ {!!})
-}

data CounterMethod A : 𝒰 where
  super : CellMethod A → CounterMethod A
  stats : CounterMethod A

pattern getᶜ = super get
pattern putᶜ x = super (put x)

StatsCellI : 𝒰 → Interface
StatsCellI A .Method = CounterMethod A
StatsCellI A .Result (super m) = Result (CellI A) m
StatsCellI A .Result  stats    = ⊤

CounterC : 𝒰
CounterC = IOObj ConsoleInterface (StatsCellI String)

counterCell : CellC → (ngets nputs : ℕ) → CounterC
counterCell = fix λ c▹ c ngets nputs →
  record { mth =
    λ where
       getᶜ     → c .mth get >>=ᵢ
                      λ where
                          (s , c′) → ret (s , (c▹ ⊛ c′ ⊛ next (suc ngets) ⊛ next nputs))
       (putᶜ x) → c .mth (put x) >>=ᵢ
                      λ where
                           (_ , c′) → ret (tt , (c▹ ⊛ c′ ⊛ next ngets ⊛ next (suc nputs)))
       stats    → bnd (putStrLn ("Counted " ++ₛ show-ℕ ngets ++ₛ " calls to get and " ++ₛ show-ℕ nputs ++ₛ " calls to put."))
                      λ _ → next (ret (tt , (c▹ ⊛ next c ⊛ next ngets ⊛ next nputs)))
  }
