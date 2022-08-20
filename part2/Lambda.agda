module part2.Lambda where

open import Data.Bool using (Bool; true; false; T; not)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using (List; _∷_; [])
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (∃-syntax; _×_)
open import Data.String using (String; _≟_)
open import Data.Unit using (tt)
open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Relation.Nullary.Decidable using (False; toWitnessFalse)
open import Relation.Nullary.Negation using (¬?)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl)

{-
  Syntax of terms

  L, M, N  ::=
    ` x  |  ƛ x ⇒ N  |  L · M  |                         # Lambda calculus
    `zero  |  `suc M  |  case L [zero⇒ M |suc x ⇒ N ]  | # Naturals
    μ x ⇒ M                                              # Fixpoint. For recursion
-}
Id : Set
Id = String

infix 5 ƛ_⇒_
infix 5 μ_⇒_
infixl 7 _·_
infix 8 `suc_
infix 9 `_

data Term : Set where
  -- Core lambda calculus
  `_                   : Id → Term          -- Variables
  ƛ_⇒_                 : Id → Term → Term   -- Abstractions
  _·_                  : Term → Term → Term -- Applications
  -- Natural numbers
  `zero                : Term                           -- Zero
  `suc_                : Term → Term                    -- Succesor
  case_[zero⇒_|suc_⇒_] : Term → Term → Id → Term → Term -- Case
  -- Recursion
  μ_⇒_                 : Id → Term → Term -- Fixpoint

-- Examples
two : Term
two = `suc `suc `zero

plus : Term
plus = μ "+" ⇒ ƛ "m" ⇒ ƛ "n" ⇒
  case ` "m" 
    [zero⇒     ` "n"
    |suc "m" ⇒ `suc (` "+" · ` "m" · ` "n")
    ]

{-
  Church numerals
  The number n is represented by a function that accepts two arguments and applies the
  first one, n times to the second one

  ChurchNat : (a -> a) -> a -> a

  zero s z = z

  one s z = s z

  two s z = s (s z)

  three s z = s (s (s z))

  n s z = s (s .. (s z))

  suc : ChurchNat -> ChurchNat
  suc n = \ s z -> s (n s z)

  plus : ChurchNat -> ChurchNat -> ChurchNat
  plus m n = \ s -> m s . n s

  mul : ChurchNat -> ChurchNat -> ChurchNat
  mul m n = \ s -> m (n s) z
-}
twoᶜ : Term
twoᶜ = ƛ "s" ⇒ ƛ "z" ⇒ ` "s" · (` "s" · ` "z")

plusᶜ : Term
plusᶜ = ƛ "m" ⇒ ƛ "n" ⇒ ƛ "s" ⇒ ƛ "z" ⇒
  ` "m" · ` "s" · (` "n" · ` "s" · ` "z")

sucᶜ : Term
sucᶜ = ƛ "n" ⇒ `suc (` "n")

-- Exercise mul
mul : Term
mul = μ "*" ⇒ ƛ "m" ⇒ ƛ "n" ⇒ 
  case ` "m"
    [zero⇒     `zero
    |suc "m" ⇒ plus · ` "n" · (` "*" · ` "m" · ` "n")
    ]

-- Exercise mulᶜ
mulᶜ : Term
mulᶜ = ƛ "m" ⇒ ƛ "n" ⇒ ƛ "s" ⇒ ƛ "z" ⇒ 
  ` "m" · (` "n" · ` "s") · ` "z"