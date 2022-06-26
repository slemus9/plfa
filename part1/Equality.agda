module part1.Equality where 

{-
  For any type A, and for any x of type A, the 
  constructor refl provides evidence that x ≡ x 
  (every value is equal to itself)

  The first argument to _≡_ is given by the parameter x : A, 
  while the second is given by an index in A → Set

  An equivalence relation is one which is reflexive, symmetric, and transitive.
-}
data _≡_ {A : Set} (x : A) : A → Set where
  refl : x ≡ x

infix 4 _≡_

{-
  The argument of sym has the type x ≡ y. When doing patter matching,
  this argument is instantiated with refl, which requires x and y
  to be the same. This means that we need evidence for x ≡ x, which is 
  given by refl.

  Agda know that, when pattern matching against refl, x and y must be the
  same
-}
sym : ∀ {A : Set} {x y : A}
  → x ≡ y
    -----
  → y ≡ x
sym refl = refl

trans : ∀ {A : Set} {x y z : A}
  → x ≡ y
  → y ≡ z
    -----
  → x ≡ z
trans refl refl = refl

cong : ∀ {A B : Set} (f : A → B) {x y : A}
  → x ≡ y
  → f x ≡ f y
cong f refl = refl

cong₂ : ∀ {A B C : Set} (f : A → B → C) {u x : A} {v y : B}
  → u ≡ x
  → v ≡ y
    -------------
  → f u v ≡ f x y
cong₂ f refl refl = refl

cong-app : ∀ {A B : Set} {f g : A → B}
  → f ≡ g
    ---------------------
  → ∀ (x : A) → f x ≡ g x
cong-app refl x = refl

{-
  If two values are equal and a predicate holds for 
  the first value, then the predicate holds for the
  second value 
-}
subs : ∀ {A : Set} {x y : A} (P : A → Set)
  → x ≡ y
    ---------
  → P x → P y
subs P refl Px = Px

-- Nested module
module ≡-Reasoning {A : Set} where

  infix  1 begin_
  infixr 2 _≡⟨⟩_ _≡⟨_⟩_
  infix  3 _∎

  begin_ : ∀ {x y : A}
    → x ≡ y
      -----
    → x ≡ y 
  begin x≡y = x≡y

  _≡⟨⟩_ : ∀ (x : A) {y : A}
    → x ≡ y
      -----
    → x ≡ y
  x ≡⟨⟩ x≡y = x≡y

  _≡⟨_⟩_ : ∀ (x : A) {y z : A}
    → x ≡ y
    → y ≡ z
      -----
    → x ≡ z
  x ≡⟨ x≡y ⟩ y≡z = trans x≡y y≡z

  _∎ : ∀ (x : A)
      -----
    → x ≡ x
  x ∎ = refl

open ≡-Reasoning

trans′ : ∀ {A : Set} {x y z : A}
  → x ≡ y
  → y ≡ z
    -----
  → x ≡ z
trans′ {A} {x} {y} {z} x≡y y≡z = 
  -- begin (x ≡⟨ x≡y ⟩ (y ≡⟨ y≡z ⟩ (z ∎)))
  -- trans x≡y (trans y≡z refl)
  -- trans x≡y y≡z
  begin 
    x
  ≡⟨ x≡y ⟩
    y
  ≡⟨ y≡z ⟩
    z
  ∎

-- Chains of equations
data ℕ : Set where
  zero : ℕ
  suc  : ℕ → ℕ

_+_ : ℕ → ℕ → ℕ
zero    + n  =  n
(suc m) + n  =  suc (m + n)

postulate
  +-identity : ∀ (m : ℕ) → m + zero ≡ m
  +-suc : ∀ (m n : ℕ) → m + suc n ≡ suc (m + n)

+-comm : ∀ (m n : ℕ) → m + n ≡ n + m
+-comm m zero =
  begin
    m + zero
  ≡⟨ +-identity m ⟩
    m
  ≡⟨⟩
    zero + m
  ∎ 
+-comm m (suc n) =
  begin
    m + suc n
  ≡⟨ +-suc m n ⟩
    suc (m + n)  
  ≡⟨ cong suc (+-comm m n) ⟩
    suc (n + m)
  ≡⟨⟩
    suc n + m
  ∎ 

-- Exercise ≤-Reasoning

data _≤_ : ℕ → ℕ → Set where

  z≤n : ∀ {n : ℕ}
    ----------
    → zero ≤ n

  s≤s : ∀ {m n : ℕ}
    → m ≤ n
    ----------
    → suc m ≤ suc n

infix 4 _≤_

≤-trans : ∀ {m n p : ℕ}
  → m ≤ n
  → n ≤ p
    -----
  → m ≤ p
≤-trans z≤n _               = z≤n
≤-trans (s≤s m≤n) (s≤s n≤p) = s≤s (≤-trans m≤n n≤p)

≤-refl : ∀ {n : ℕ}
    -----
  → n ≤ n
≤-refl {zero}   = z≤n
≤-refl {suc n}  = s≤s ≤-refl

≤-refl-≡ : ∀ {m n : ℕ}
  → m ≡ n
    -----
  → m ≤ n
≤-refl-≡ refl = ≤-refl


module ≤-Reasoning where

  infix  1 ≤-begin_
  infixr 2 _≤⟨⟩_ _≤⟨_⟩_
  infix  3 _≤∎

  ≤-begin_ : ∀ {x y : ℕ}
    → x ≤ y
      -----
    → x ≤ y
  ≤-begin_ x≤y = x≤y

  _≤⟨⟩_ : ∀ (x : ℕ) {y : ℕ}
    → x ≤ y
      -----
    → x ≤ y
  x ≤⟨⟩ x≤y = x≤y

  _≤⟨_⟩_ : ∀ (x : ℕ) {y z : ℕ}
    → x ≤ y
    → y ≤ z
      -----
    → x ≤ z
  x ≤⟨ x≤y ⟩ y≤z = ≤-trans x≤y y≤z

  _≤∎ : ∀ (x : ℕ)
      -----
    → x ≤ x
  x ≤∎ = ≤-refl

open ≤-Reasoning

+-monoʳ-≤ : ∀ (n p q : ℕ)
  → p ≤ q
    -------------
  → n + p ≤ n + q
+-monoʳ-≤ zero p q p≤q = 
  ≤-begin
    zero + p
  ≤⟨⟩
    p
  ≤⟨ p≤q ⟩
    q
  ≤⟨⟩
    zero + q
  ≤∎
+-monoʳ-≤ (suc n) p q p≤q =
  ≤-begin
    suc n + p
  ≤⟨⟩
    suc (n + p)
  ≤⟨ s≤s (+-monoʳ-≤ n p q p≤q) ⟩
    suc (n + q)
  ≤⟨⟩
    suc n + q
  ≤∎

+-monoˡ-≤ : ∀ (m n p : ℕ)
  → m ≤ n
    -------------
  → m + p ≤ n + p
+-monoˡ-≤ m n p m≤n =
  ≤-begin
    m + p
  ≤⟨ ≤-refl-≡ (+-comm m p) ⟩
    p + m
  ≤⟨ +-monoʳ-≤ p m n m≤n ⟩
    p + n
  ≤⟨ ≤-refl-≡ (+-comm p n) ⟩
    n + p
  ≤∎

+-mono-≤ : ∀ (m n p q : ℕ)
  → m ≤ n
  → p ≤ q
    -------------
  → m + p ≤ n + q
+-mono-≤ m n p q m≤n p≤q = 
  ≤-begin
    m + p
  ≤⟨ +-monoʳ-≤ m p q p≤q ⟩
    m + q
  ≤⟨ +-monoˡ-≤ m n q m≤n ⟩
    n + q
  ≤∎

-- Rewriting
data even : ℕ → Set
data odd  : ℕ → Set

data even where

  even-zero : even zero

  even-suc : ∀ {n : ℕ}
    → odd n
      ------------
    → even (suc n)

data odd where
  odd-suc : ∀ {n : ℕ}
    → even n
      -----------
    → odd (suc n)

{-# BUILTIN EQUALITY _≡_ #-}

even-comm : ∀ (m n : ℕ)
  → even (m + n)
    ------------
  → even (n + m)
even-comm m n ev 
  rewrite +-comm m n = ev

+-comm′ : ∀ (m n : ℕ) → m + n ≡ n + m
+-comm′ zero    n  rewrite +-identity n             =  refl
+-comm′ (suc m) n  rewrite +-suc n m | +-comm′ m n  =  refl

-- Leibniz Equality
_≐_ : ∀ {A : Set} (x y : A) → Set₁
_≐_ {A} x y = ∀ (P : A → Set) → P x → P y

{-
  Might be helpful to think of the type signature as
    refl-≐ : ∀ {A : Set} {x : A}
      → ∀ (P : A → Set) → P x → P x
-}
refl-≐ : ∀ {A : Set} {x : A}
  → x ≐ x
refl-≐ P Px = Px

{-
  trans-≐ : ∀ {A : Set} {x y z : A}
    → x ≐ y
    → y ≐ z
      -----
    → ∀ (P : A → Set) → P x → P z
-}
trans-≐ : ∀ {A : Set} {x y z : A}
  → x ≐ y
  → y ≐ z
    -----
  → x ≐ z
trans-≐ x≐y y≐z P Px = y≐z P (x≐y P Px)

{-
  sym-≐ : ∀ {A : Set} {x y : A}
    → x ≐ y
      -----
    → ∀ (P : A → Set) → P x → P y
-}
sym-≐ : ∀ {A : Set} {x y : A}
  → x ≐ y
    -----
  → y ≐ x
sym-≐ {A} {x} {y} x≐y P = Qy
  where
    Q : A → Set
    Q z = P z → P x

    -- Qx : P x → P x
    Qx : Q x
    Qx = refl-≐ P

    {-    
      x≐y : ∀ (P : A → Set) → P x → P y
      x≐y Q : Q x → Q y
      x≐y Q Qx : Q y
      x≐y Q Qx : P y → P x
    -}
    Qy : Q y
    Qy = x≐y Q Qx

{-
  ≡-implies-≐ : ∀ {A : Set} {x y : A}
    → x ≡ y
      -----
    → ∀ (P : A → Set) → P x → P y
-}
≡-implies-≐ : ∀ {A : Set} {x y : A}
  → x ≡ y
    -----
  → x ≐ y
≡-implies-≐ x≡y P = subs P x≡y

{-
  ≐-implies-≡ : ∀ {A : Set} {x y : A}
    → ∀ (P : A → Set) → P x → P y
      -----
    → x ≡ y
-}
≐-implies-≡ : ∀ {A : Set} {x y : A}
  → x ≐ y
    -----
  → x ≡ y
≐-implies-≡ {A} {x} {y} x≐y = Qy
  where
    Q : A → Set
    Q z = x ≡ z

    Qx : Q x
    Qx = refl

    Qy : Q y
    Qy = x≐y Q Qx