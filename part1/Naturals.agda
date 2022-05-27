module part1.Naturals where

-- ℕ is a type
data ℕ : Set where
  zero : ℕ -- Base case: zero is a Natural number
  suc  : ℕ → ℕ -- Inductive case: is m is a Natural number, suc m is also a Natural number

{-
  Pragma that allows to use shorthands for writing
  the natural numbers (0 instead of zero, 1 instead of suc zero, and so on).
  It also enables an efficient internal representation using Haskell's 
  arbitrary-precision integers
-}
{-# BUILTIN NATURAL ℕ #-}

import Relation.Binary.PropositionalEquality as Eq
-- adds all the names specified in the using clause, into the current scope
open Eq using (_≡_; refl)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; _∎)

{- 
  Addition:
  0       + n  ≡  n
  (1 + m) + n  ≡  1 + (m + n)
-}
_+_ : ℕ → ℕ → ℕ
zero + n = n
(suc m) + n = suc (m + n)


{-
  Example:

  _ is a dummy name that can be reused.
  Here the type is 2 + 3 ≡ 5, and the term is a chain of equations that provide evidence.
  Type as a Proposition and Term as Evidence (Proof)
-}
_ : 2 + 3 ≡ 5
_ =
  begin
    2 + 3
  ≡⟨⟩    -- is shorthand for
    (suc (suc zero)) + (suc (suc (suc zero)))
  ≡⟨⟩    -- inductive case
    suc ((suc zero) + (suc (suc (suc zero))))
  ≡⟨⟩    -- inductive case
    suc (suc (zero + (suc (suc (suc zero)))))
  ≡⟨⟩    -- base case
    suc (suc (suc (suc (suc zero))))
  ≡⟨⟩    -- is longhand for
    5
  ∎

_ : 2 + 3 ≡ 5
_ =
  begin
    2 + 3
  ≡⟨⟩
    suc (1 + 3)
  ≡⟨⟩
    suc (suc (0 + 3))
  ≡⟨⟩
    suc (suc 3)
  ≡⟨⟩
    5
  ∎

{-
  A binary relation is reflexive if every value relates to itself.
  The evidence that a value is equal to itself is written using 
  relf
-}
_ : 2 + 3 ≡ 5
_ = refl

{-
  Exercise:

  Compute 3 + 4, writing out your reasoning as a chain of equations, using the equations for +.
-}
_ : 3 + 4 ≡ 7
_ = 
  begin
    3 + 4
  ≡⟨⟩ -- inductive case
    suc (2 + 4)
  ≡⟨⟩ -- 2 = suc 1
    suc (suc 1 + 4)
  ≡⟨⟩ -- inductive case
    suc (suc (1 + 4))
  ≡⟨⟩ -- 1 = suc 0
    suc (suc (suc 0 + 4))
  ≡⟨⟩ -- inductive case
    suc (suc (suc (0 + 4)))
  ≡⟨⟩ -- base case
    suc (suc (suc 4))
  ≡⟨⟩ -- simplify
    7
  ∎

{-
  Multiplication: 
  0       * n  ≡  0
  (1 + m) * n  ≡  n + (m * n)
-}
_*_ : ℕ → ℕ → ℕ
zero * n    = zero
(suc m) * n = n + (m * n)

_ =
  begin
    2 * 3
  ≡⟨⟩    -- inductive case
    3 + (1 * 3)
  ≡⟨⟩    -- inductive case
    3 + (3 + (0 * 3))
  ≡⟨⟩    -- base case
    3 + (3 + 0)
  ≡⟨⟩    -- simplify
    6
  ∎

{-
  Exercise: 

  Compute 3 * 4, writing out your reasoning as a chain of equations, using the equations for *. 
  (You do not need to step through the evaluation of +.)
-}
_ =
  begin
    3 * 4
  ≡⟨⟩ -- inductive case
    4 + (2 * 4)
  ≡⟨⟩ -- inductive case
    4 + (4 + (1 * 4))
  ≡⟨⟩ -- inductive case
    4 + (4 + (4 + (0 * 4)))
  ≡⟨⟩ -- base case
    4 + (4 + (4 + 0))
  ≡⟨⟩ -- simplify
    12
  ∎

{-
  Exercise:

  Define exponentiation.
  m ^ 0        =  1
  m ^ (1 + n)  =  m * (m ^ n)
-}
_^_ : ℕ → ℕ → ℕ
m ^ 0 = 1
m ^ (suc n) = m * (m ^ n)

{-
  Monus: 

  Subtraction but, since there are no negative natural numbers,
  if we subtract a larger number from a smaller one, we get zero
-}
_∸_ : ℕ → ℕ → ℕ
m     ∸ zero = m
zero  ∸ n = zero
suc m ∸ suc n = m ∸ n

{-
  Exercise:

  Compute 5 ∸ 3 and 3 ∸ 5, writing out your reasoning as a chain of equations.
-}
_ = 
  begin 
    5 ∸ 3
  ≡⟨⟩ -- suc m ∸ suc n = m ∸ n
    4 ∸ 2
  ≡⟨⟩ -- suc m ∸ suc n = m ∸ n
    3 ∸ 1
  ≡⟨⟩ -- suc m ∸ suc n = m ∸ n
    2 ∸ 0
  ≡⟨⟩ -- m ∸ zero = m
    2
  ∎

_ = 
  begin 
    3 ∸ 5
  ≡⟨⟩ -- suc m ∸ suc n = m ∸ n
    2 ∸ 4
  ≡⟨⟩ -- suc m ∸ suc n = m ∸ n
    1 ∸ 3
  ≡⟨⟩ -- suc m ∸ suc n = m ∸ n
    0 ∸ 2
  ≡⟨⟩ -- zero ∸ n = zero
    0
  ∎

-- Precedence
-- infixl associates to the left, and infixr to the right
infixl 6  _+_  _∸_
infixl 7  _*_

-- Use the usual efficient representation
{-# BUILTIN NATPLUS _+_ #-}
{-# BUILTIN NATTIMES _*_ #-}
{-# BUILTIN NATMINUS _∸_ #-}

{-
  Bitstring

  A more efficient representation of natural numbers
-}
data Bin : Set where
  ⟨⟩ : Bin
  _O : Bin → Bin
  _I : Bin → Bin

_ = ⟨⟩ I O I I -- Represents 1011

{-
  Exercise:

  define:

  inc: Bin → Bin - increments a natural number by one in the Bin respresentation
  to: ℕ → Bin 
  from: Bin → ℕ

  (Notes on the solution at Naturals.md)
-}
inc : Bin → Bin
inc ⟨⟩ = ⟨⟩ I
inc (b O) = b I
inc (b I) = (inc b) O

_ : inc (⟨⟩ O) ≡ ⟨⟩ I
_ = refl

_ : inc (⟨⟩ I) ≡ ⟨⟩ I O
_ = refl

_ : inc (⟨⟩ I O) ≡ ⟨⟩ I I
_ = refl

_ : inc (⟨⟩ I I) ≡ ⟨⟩ I O O
_ = refl

_ : inc (⟨⟩ I O O) ≡ ⟨⟩ I O I
_ = refl

_ : inc (⟨⟩ I O I) ≡ ⟨⟩ I I O
_ = refl

_ : inc (⟨⟩ I O I I) ≡ ⟨⟩ I I O O
_ = refl