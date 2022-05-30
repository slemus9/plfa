module part1.Relations where 

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong)
open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Nat.Properties using (+-comm; +-identityʳ)

{-
  Less than or equal. Inference rules:

  z≤n --------
      zero ≤ n

      m ≤ n
  s≤s -------------
      suc m ≤ suc n

  In the definition below, z≤n and s≤s are constructors,
  while zero ≤ n, m ≤ n, and suc m ≤ suc n are types.

  This is an indexed data type where the type m ≤ n is 
  indexed by the naturals m and n
-}
data _≤_ : ℕ → ℕ → Set where

  {-
    Base case:
    for all naturals, the proposition zero ≤ n holds.

    The constructor z≤n provides evidence that zero ≤ n holds
  -}
  z≤n : ∀ {n : ℕ}
    ----------
    → zero ≤ n
  
  {-
    Inductive case:
    for all naturals n and m, if the proposition m ≤ n holds,
    then suc m ≤ suc n also holds.

    The constructor s≤s takes evidence that m ≤ n holds into evidence 
    that suc m ≤ suc n holds.

    Arguments inside curly braces {} (rather than parentheses ()) are 
    implicit; agda's typechecker will infer them
  -}
  s≤s : ∀ {m n : ℕ}
    → m ≤ n
    ----------
    → suc m ≤ suc n

{-
  z≤n -----
      0 ≤ 2
 s≤s -------
      1 ≤ 3
s≤s ---------
      2 ≤ 4
-}
_ : 2 ≤ 4
_ = s≤s (s≤s z≤n)

-- We can also write it with explicit arguments
_ : 2 ≤ 4
_ = s≤s {1} {3} (s≤s {0} {2} (z≤n {2}))

_ : 2 ≤ 4
_ = s≤s {m = 1} {n = 3} (s≤s {m = 0} {n = 2} (z≤n {n = 2}))

_ : 2 ≤ 4
_ = s≤s {n = 3} (s≤s {n = 2} z≤n)

-- We can ask Agda to infer an explicit term
-- Here, there is only one value which gives us the correct proof: m
+-identityʳ′ : ∀ {m : ℕ} → m + zero ≡ m
+-identityʳ′ = +-identityʳ _

infix 4 _≤_

-- Inverting rules
inv-s≤s : ∀ {m n : ℕ}
  → suc m ≤ suc n
    -------------
  → m ≤ n
inv-s≤s (s≤s m≤n) = m≤n

-- There is only one way a number can be less or equal to 0
inv-z≤n : ∀ {m : ℕ}
  → m ≤ zero
    --------
  → m ≡ zero
inv-z≤n z≤n = refl

-- Properties of ordering relations

-- Reflexivity
≤-refl : ∀ {n : ℕ}
    -----
  → n ≤ n
≤-refl {zero}   = z≤n
{-
  Inductive case:
  the inductive hypothesis ≤-refl {n} gives us evidence of
  n ≤ n, which then it's used with s≤s to provide evidence for
  suc n ≤ suc n
-}
≤-refl {suc n}  = s≤s ≤-refl

-- Transitivity
-- Induction over the evidence that m ≤ n
≤-trans : ∀ {m n p : ℕ}
  → m ≤ n
  → n ≤ p
    -----
  → m ≤ p
{-
  Base case: 
  we have to show that 0 ≤ p holds, which follows
  immediatedly by the evidence z≤n
-}
≤-trans z≤n _               = z≤n
{-
  Inductive case:
  We have evidence that suc m ≤ suc n and suc n ≤ suc p hold 
  (with (s≤s m≤n) and (s≤s n≤p) respectively) and we must show
  that suc m ≤ suc p.

  The inductive hypothesis ≤-trans m≤n n≤p gives us evidence that
  m ≤ p, so we only have to apply s≤s to the hypothesis to get
  evidence for suc m ≤ suc p.

  We are using induction on evidence that a certain property holds,
  rather than induction on values.

  Note that the case ≤-trans (s≤s m≤n) z≤n is not possible, since 
  the first inequality is suc m ≤ suc n, but the second inequality
  is 0 ≤ p. Agda can determine that this case cannot occur and
  it doesn't permit to be listed
-}
≤-trans (s≤s m≤n) (s≤s n≤p) = s≤s (≤-trans m≤n n≤p)

-- with explicit arguments
≤-trans′ : ∀ (m n p : ℕ)
  → m ≤ n
  → n ≤ p
    -----
  → m ≤ p
≤-trans′ zero    _       _       z≤n       _          =  z≤n
≤-trans′ (suc m) (suc n) (suc p) (s≤s m≤n) (s≤s n≤p)  =  s≤s (≤-trans′ m n p m≤n n≤p)

-- Anti-symmetry
≤-antisym : ∀ {m n : ℕ}
  → m ≤ n
  → n ≤ m
    -----
  → m ≡ n
≤-antisym z≤n z≤n = refl
{-
  Inductive Case:
  
  We have evidence for suc m ≤ suc n (s≤s m≤n) and for suc n ≤ suc m (s≤s n≤m).
  We need to prove that suc m ≡ suc n.

  ≤-antisym m≤n n≤m provides evidence that m ≡ n holds, so the proof follows
  by congruence with the suc function
-}
≤-antisym (s≤s m≤n) (s≤s n≤m) = cong suc (≤-antisym m≤n n≤m)

