module part1.Induction where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; sym)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; step-≡; _∎)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _∸_)

{-
  Proof by induction for associtivity of addition for natural numbers.

  The following signature states that +-assoc will provide evidence for
  the proposition given in the type: ∀ (m n p : ℕ) → (m + n) + p ≡ m + (n + p).

  +-assoc is a function that accepts the natural numbers m, n and p, and returns
  the evidence of the type
-}
+-assoc : ∀ (m n p : ℕ) → (m + n) + p ≡ m + (n + p)

-- Base case: (zero + n) + p ≡ zero + (n + p)
+-assoc zero n p =
  begin
    (zero + n) + p
  ≡⟨⟩
    n + p
  ≡⟨⟩
    zero + (n + p)
  ∎

{-
  Inductive case:
  (m + n) + p ≡ m + (n + p) → (suc m + n) + p ≡ suc m + (n + p)
-}
+-assoc (suc m) n p =
  begin
    (suc m + n) + p
  ≡⟨⟩
    suc (m + n) + p
  ≡⟨⟩ 
    suc ((m + n) + p)
  {-
    Use of the induction hypothesis.

    The use of _≡⟨_⟩_ here, is to provide a justification for the following 
    equation within the brackets.

    Here we have a recursive invocation to +-assoc m n p, which has the
    induction hypothesis as its type.

    A relation is said to be a congruence for a given function, if it's preserved
    when applying the function. If e is evidence that x ≡ y, then cong f e is 
    evidence that f x ≡ f y for any function f.

    In this case we are saying that if +-assoc m n p is the evidence for:

      (m + n) + p ≡ m + (n + p)

    Then cong suc (+-assoc m n p) is the evidence for:

      suc ((m + n) + p) ≡ suc (m + (n + p))

    Here, the inductive hypothesis is not being assumed, but rather it's being by a
    recursive invocation of the function that we are defining: +-assoc m n p -
    Correspondence between proof by induction and definition by recursion
  -}
  ≡⟨ cong suc (+-assoc m n p) ⟩
    suc (m + (n + p))
  ≡⟨⟩
    suc m + (n + p)
  ∎

-- Example of the correspondence between induction and recursion
+-assoc-2 : ∀ (n p : ℕ) → (2 + n) + p ≡ 2 + (n + p)
+-assoc-2 n p =
  begin
    (2 + n) + p
  ≡⟨⟩
    suc (1 + n) + p
  ≡⟨⟩
    suc ((1 + n) + p)
  ≡⟨ cong suc (+-assoc-1 n p) ⟩
    suc (1 + (n + p))
  ≡⟨⟩
    2 + (n + p)
  ∎
  where
  +-assoc-1 : ∀ (n p : ℕ) → (1 + n) + p ≡ 1 + (n + p)
  +-assoc-1 n p =
    begin
      (1 + n) + p
    ≡⟨⟩
      suc (0 + n) + p
    ≡⟨⟩
      suc ((0 + n) + p)
    ≡⟨ cong suc (+-assoc-0 n p) ⟩
      suc (0 + (n + p))
    ≡⟨⟩
      1 + (n + p)
    ∎
    where
    +-assoc-0 : ∀ (n p : ℕ) → (0 + n) + p ≡ 0 + (n + p)
    +-assoc-0 n p =
      begin
        (0 + n) + p
      ≡⟨⟩
        n + p
      ≡⟨⟩
        0 + (n + p)
      ∎

-- Proof for commutativity: m + n ≡ n + m
-- Requires 2 lemmas

-- First lemma - identity
-- the lemma states that zero is right-identity
+-identityʳ : ∀ (m : ℕ) → m + zero ≡ m

-- Base case states that zero is a left-identity
+-identityʳ zero =
  begin
    zero + zero 
  ≡⟨⟩
    zero
  ∎

{-
  Inductive case:
  m + zero ≡ m → suc m + zero ≡ suc m
-}
+-identityʳ (suc m) = 
  begin 
    suc m + zero
  ≡⟨⟩
    suc (m + zero)
  ≡⟨ cong suc (+-identityʳ m) ⟩
    suc m
  ∎

-- Second lemma: m + suc n ≡ suc (m + n)

+-suc : ∀ (m n : ℕ) → m + suc n ≡ suc (m + n)

-- Base case: zero + suc n ≡ suc (zero + n)
+-suc zero n =
  begin 
    zero + suc n
  ≡⟨⟩
    suc n
  ≡⟨⟩
    suc (zero + n)
  ∎

{-
  Inductive case:
  m + suc n ≡ suc (m + n) → suc m + suc n ≡ suc (suc m + n)
-}
+-suc (suc m) n =
  begin
    suc m + suc n
  ≡⟨⟩
    suc (m + suc n)
  ≡⟨ cong suc (+-suc m n) ⟩
    suc (suc (m + n))
  ≡⟨⟩
    suc (suc m + n)
  ∎

+-comm : ∀ (m n : ℕ) → m + n ≡ n + m
-- Base case: m + zero ≡ zero + n
+-comm m zero =
  begin
    m + zero
  ≡⟨ +-identityʳ m ⟩
    m
  ≡⟨⟩
    zero + m
  ∎
{-
  Inductive case:
  m + n ≡ n + m → m + suc n ≡ suc n + m
-}
+-comm m (suc n) =
  begin 
    m + suc n
  ≡⟨ +-suc m n ⟩
    suc (m + n)
  ≡⟨ cong suc (+-comm m n) ⟩
    suc (n + m)
  ∎

+-rearrange : ∀ (m n p q : ℕ) → (m + n) + (p + q) ≡ m + (n + p) + q
+-rearrange m n p q =
  begin
    (m + n) + (p + q)
  ≡⟨ +-assoc m n (p + q) ⟩
    m + (n + (p + q))
  {-
    sym interchanges the sides of an equation; if e provides evidence to x ≡ y,
    then sym e provides evidence to y ≡ x.


    +-assoc n p q : (n + p) + q ≡ n + (p + q)
    sym (+-assoc n p q) : n + (p + q) ≡ (n + p) + q

    (x +_) is the function (x +_) y = x + y, so the final equation is:
    cong (m +_) (sym (+-assoc n p q)) : m + (n + (p + q)) ≡ m + ((n + p) + q)
  -}
  ≡⟨ cong (m +_) (sym (+-assoc n p q)) ⟩
    m + ((n + p) + q)
  ≡⟨ sym (+-assoc m (n + p) q) ⟩
  {-
    Addition associates to the left, so: 
    (m + (n + p)) + q ≡ m + (n + p) + q
  -}
    (m + (n + p)) + q
  ∎

{-
  Exercise: finite-|-assoc

  (see Induction.md)
-}



