module part1.Relations where 

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_)
open import Data.Nat.Properties using (+-comm; +-identityʳ; *-comm)

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

{-
  Total:

  for any naturals m and n either m ≤ n or n ≤ m, or both if m and n are equal.
-}
data Total (m n : ℕ) : Set where

  forward :
      m ≤ n
      ---------
    → Total m n

  flipped :
      n ≤ m
      ---------
    → Total m n

≤-total : ∀ (m n : ℕ) → Total m n 
≤-total zero n = forward z≤n
≤-total (suc m) zero = flipped z≤n
-- The with clause allows pattern matching for ≤-total m n
≤-total (suc m) (suc n) 
    with ≤-total m n 
... | forward m≤n = forward (s≤s m≤n)
... | flipped n≤m = flipped (s≤s n≤m)

≤-total′ : ∀ (m n : ℕ) → Total m n
≤-total′ zero    n        =  forward z≤n
≤-total′ (suc m) zero     =  flipped z≤n
≤-total′ (suc m) (suc n)  =  helper (≤-total′ m n)
  where
  helper : Total m n → Total (suc m) (suc n)
  helper (forward m≤n)  =  forward (s≤s m≤n)
  helper (flipped n≤m)  =  flipped (s≤s n≤m)

-- Monotonicity

{-
  Addition is monotonic with regard to inequality:
  ∀ {m n p q : ℕ} → m ≤ n → p ≤ q → m + p ≤ n + q
-}
+-monoʳ-≤ : ∀ (n p q : ℕ)
  → p ≤ q
    -------------
  → n + p ≤ n + q
+-monoʳ-≤ zero p q p≤q = p≤q
+-monoʳ-≤ (suc n) p q p≤q = s≤s (+-monoʳ-≤ n p q p≤q)

+-monoˡ-≤ : ∀ (m n p : ℕ)
  → m ≤ n
    -------------
  → m + p ≤ n + p
+-monoˡ-≤ m n p m≤n 
  rewrite (+-comm m p ) 
  | +-comm n p = +-monoʳ-≤ p m n m≤n

+-mono-≤ : ∀ (m n p q : ℕ)
  → m ≤ n
  → p ≤ q
    -------------
  → m + p ≤ n + q
+-mono-≤ m n p q m≤n p≤q  =  ≤-trans (+-monoˡ-≤ m n p m≤n) (+-monoʳ-≤ n p q p≤q)

{-
  Exercise *-mono-≤:

  Show that multiplication is monotonic with regard to inequality.
-}
*-monoʳ-≤ : ∀ (n p q : ℕ) 
  → p ≤ q 
    -------------
  → n * p ≤ n * q
*-monoʳ-≤ zero _ _ _ = z≤n
*-monoʳ-≤ (suc n) p q p≤n = +-mono-≤ p q (n * p) (n * q) p≤n np≤nq
  where
    np≤nq = *-monoʳ-≤ n p q p≤n

*-monoˡ-≤ : ∀ (m n p : ℕ)
  → m ≤ n
    -------------
  → m * p ≤ n * p
*-monoˡ-≤ m n p m≤n 
  rewrite *-comm m p 
  | *-comm n p = *-monoʳ-≤ p m n m≤n

*-mono-≤ : ∀ (m n p q : ℕ)
  → m ≤ n
  → p ≤ q
    -------------
  → m * p ≤ n * q
*-mono-≤ m n p q m≤n p≤q = ≤-trans (*-monoˡ-≤ m n p m≤n) (*-monoʳ-≤ n p q p≤q)


infix 4 _<_

{-
  Strict inequality 
  
  It is irreflexive. n < n never holds for any value n.

  It is not total, but satisfies the property of Trichotomy.
  For any m and n, exactly one of the following hold: m < n, m ≡ n or m > n

  It is monotonic with regards to addition and multiplication
-}
data _<_ : ℕ → ℕ → Set where

  z<s : ∀ {n : ℕ}
      ------------
    → zero < suc n

  s<s : ∀ {m n : ℕ}
    → m < n
      -------------
    → suc m < suc n

-- Exercise: <-trans
<-trans : ∀ {m n p : ℕ}
  → m < n
  → n < p
    -----
  → m < p
<-trans z<s (s<s _) = z<s
<-trans (s<s m<n) (s<s n<p) = s<s (<-trans m<n n<p)

{-
  Exercise: trichotomy
  Show that strict inequality satisfies a weak version of trichotomy, in the sense that for any 
  m and n that one of the following holds: m < n, m ≡ n, or m > n.

  Define m > n to be the same as n < m
-}
data WeakTrichotomy (m n : ℕ): Set where

  forward :
      m < n
      ------------------
    → WeakTrichotomy m n

  equiv :
      m ≡ n
      ------------------
    → WeakTrichotomy m n
  
  flipped :
      n < m
      ------------------
    → WeakTrichotomy m n

<-weakTrich : ∀ (m n : ℕ) → WeakTrichotomy m n
<-weakTrich zero zero = equiv refl
<-weakTrich zero (suc n) = forward z<s
<-weakTrich (suc m) zero = flipped z<s
<-weakTrich (suc m) (suc n) 
    with <-weakTrich m n 
... | forward m<n = forward (s<s m<n)
... | equiv   m≡n = equiv (cong suc m≡n)
... | flipped n<m = flipped (s<s n<m)

-- Exercise: +-mono-<
+-monoʳ-< : ∀ (n p q : ℕ)
  → p < q
    -------------
  → n + p < n + q
+-monoʳ-< zero p q p<q = p<q
+-monoʳ-< (suc n) p q p<q = s<s (+-monoʳ-< n p q p<q)

+-monoˡ-< : ∀ (m n p : ℕ)
  → m < n
    -------------
  → m + p < n + p
+-monoˡ-< m n p m<n 
  rewrite +-comm m p 
  | +-comm n p = +-monoʳ-< p m n m<n

+-mono-< : ∀ (m n p q : ℕ)
  → m < n
  → p < q
    -------------
  → m + p < n + q
+-mono-< m n p q m<n p<q = <-trans (+-monoˡ-< m n p m<n) (+-monoʳ-< n p q p<q)

-- Exercise: ≤-iff-<
≤-iffˡ-< : ∀ {m n : ℕ}
  → suc m ≤ n
    -----
  → m < n
≤-iffˡ-< {zero} {suc n} _ = z<s
≤-iffˡ-< {suc m} {suc n} (s≤s m≤n) = s<s (≤-iffˡ-< m≤n)


≤-iffʳ-< : ∀ {m n : ℕ}
  → m < n
    ---------
  → suc m ≤ n
≤-iffʳ-< {zero} {suc n} _ = s≤s z≤n
≤-iffʳ-< {suc m} {suc n} (s<s m<n) = s≤s (≤-iffʳ-< m<n)

{-
  Exercise: <-trans-revisited

  suc m ≤ n 
  suc n ≤ p
  n ≤ suc n 
-}
n≤sucn : ∀ {n : ℕ} → n ≤ suc n
n≤sucn {n} = +-monoˡ-≤ 0 1 n z≤n

<-trans-revisited : ∀ {m n p : ℕ}
  → m < n 
  → n < p
    -----
  → m < p
<-trans-revisited m<n n<p = ≤-iffˡ-< sucm≤p
  where
    sucm≤n  = ≤-iffʳ-< m<n
    sucn≤p  = ≤-iffʳ-< n<p
    n≤p     = ≤-trans n≤sucn sucn≤p
    sucm≤p  = ≤-trans sucm≤n n≤p

-- Even and Odd
data even : ℕ → Set
data odd  : ℕ → Set

{-
  Even and Odd are mutually recursive.
  
  Even is zero, or the successor of an odd number
  Odd is the successor of an even number
-}
data even where

  zero :
    ---------
    even zero

  suc  : ∀ {n : ℕ}
    → odd n
      ------------
    → even (suc n)

data odd where

  suc  : ∀ {n : ℕ}
    → even n
      -----------
    → odd (suc n)

e+e≡e : ∀ {m n : ℕ}
  → even m
  → even n
    ------------
  → even (m + n)

o+e≡o : ∀ {m n : ℕ}
  → odd m
  → even n
    -----------
  → odd (m + n)

e+e≡e zero nIsEven = nIsEven
e+e≡e (suc mIsOdd) nIsEven = suc (o+e≡o mIsOdd nIsEven)   

o+e≡o (suc mIsEven) nIsEven = suc (e+e≡e mIsEven nIsEven)

-- Exercise: o+o≡e
o+o≡e : ∀ {m n : ℕ}
  → odd m
  → odd n
    ------------
  → even (m + n)

e+o≡o : ∀ {m n : ℕ}
  → even m
  → odd n
    -----------
  → odd (m + n)

e+o≡o zero nIsOdd = nIsOdd
e+o≡o (suc mIsOdd) nIsOdd = suc (o+o≡e mIsOdd nIsOdd)


o+o≡e (suc mIsEven) nIsOdd = suc (e+o≡o mIsEven nIsOdd)

-- Exercise: Bin-predicates
open import part1.Bin using (Bin; ⟨⟩; _O; _I; inc; to; from)

data Can : Bin → Set
data One : Bin → Set

-- Is cannonical (no leading 0s)
data Can where

  zero : 
    Can (⟨⟩ O)

  -- If b has a leading one, b is cannonical
  can : ∀ {b : Bin}
    → One b
      -----------
    → Can b 

-- b has a leading one
data One where

  -- If b is cannonical, inc b has a leading one
  suc : ∀ {b : Bin}
    → Can b
      -----------
    → One (inc b)

{-
  Show that inc preserves canonical bitstrings

  Can b
  ------------
  Can (inc b)
-}
inc-one : ∀ {b : Bin}
  → One b
    -----------
  → One (inc b)

inc-can : ∀ {b : Bin}
  → Can b
    -----------
  → Can (inc b)

inc-one (suc bCan) = suc (inc-can bCan)

inc-can zero = can (suc zero)
inc-can (can bOne) = can (inc-one bOne)
