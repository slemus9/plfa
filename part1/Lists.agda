module part1.Lists where 

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; sym; trans; cong; cong₂)
open Eq.≡-Reasoning
open import Data.Bool using (Bool; true; false; T; _∧_; _∨_; not)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _∸_; _≤_; s≤s; z≤n)
open import Data.Nat.Properties using
  ( +-assoc
  ; +-comm
  ; +-identityˡ
  ; +-identityʳ
  ; *-assoc
  ; *-comm
  ; *-identityˡ
  ; *-identityʳ
  )
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Data.Product using (_×_; ∃; ∃-syntax) renaming (_,_ to ⟨_,_⟩)
open import Function using (_∘_)
open import Level using (Level)
open import part1.Isomorphism using (_≃_; _⇔_; extensionality)

data List (A : Set) : Set where
  []  : List A
  _::_ : A → List A → List A

infixr 5 _::_

_ : List ℕ
_ = 0 :: 1 :: 2 :: []

data List′ : Set → Set where
  []′  : ∀ {A : Set} → List′ A
  _::′_ : ∀ {A : Set} → A → List′ A → List′ A

_ : List ℕ
_ = _::_ {ℕ} 0 (_::_ {ℕ} 1 (_::_ {ℕ} 2 ([] {ℕ})))

-- Tells Agda that the type List corresponds to the Haskell's list
{-# BUILTIN LIST List #-}

pattern [_] z = z :: []
pattern [_,_] y z = y :: z :: []
pattern [_,_,_] x y z = x :: y :: z :: []
pattern [_,_,_,_] w x y z = w :: x :: y :: z :: []
pattern [_,_,_,_,_] v w x y z = v :: w :: x :: y :: z :: []
pattern [_,_,_,_,_,_] u v w x y z = u :: v :: w :: x :: y :: z :: []

infixr 5 _++_

_++_ : ∀ {A : Set} → List A → List A → List A
[]        ++ ys = ys
(x :: xs) ++ ys = x :: (xs ++ ys)

-- Append is associative
++-assoc : ∀ {A : Set} (xs ys zs : List A)
  → (xs ++ ys) ++ zs ≡ xs ++ (ys ++ zs)
++-assoc [] ys zs =
  begin
    ([] ++ ys) ++ zs
  ≡⟨⟩
    ys ++ zs
  ≡⟨⟩
    [] ++ (ys ++ zs)
  ∎
++-assoc (x :: xs) ys zs =
  begin
    (x :: xs ++ ys) ++ zs
  ≡⟨⟩
    x :: (xs ++ ys) ++ zs
  ≡⟨⟩
    x :: ((xs ++ ys) ++ zs)
  ≡⟨ cong (x ::_) (++-assoc xs ys zs) ⟩
    x :: (xs ++ (ys ++ zs))
  ≡⟨⟩
    x :: xs ++ (ys ++ zs)
  ∎

-- [] is the identity
++-identityˡ : ∀ {A : Set} (xs : List A) → [] ++ xs ≡ xs
++-identityˡ xs =
  begin
    [] ++ xs
  ≡⟨⟩
    xs
  ∎

++-identityʳ : ∀ {A : Set} (xs : List A) → xs ++ [] ≡ xs
++-identityʳ [] =
  begin
    [] ++ []
  ≡⟨⟩
    []
  ∎
++-identityʳ (x :: xs) =
  begin
    (x :: xs) ++ []
  ≡⟨⟩
    x :: (xs ++ [])
  ≡⟨ cong (x ::_) (++-identityʳ xs) ⟩
    x :: xs
  ∎

-- Associativity and identity form a monoid over lists
-- Length
length : ∀ {A : Set} → List A → ℕ
length []        =  zero
length (x :: xs)  =  suc (length xs)

length-++ : ∀ {A : Set} (xs ys : List A)
  → length (xs ++ ys) ≡ length xs + length ys
length-++ {A} [] ys =
  begin
    length ([] ++ ys)
  ≡⟨⟩
    length ys
  ≡⟨⟩
    length {A} [] + length ys
  ∎
length-++ (x :: xs) ys =
  begin
    length ((x :: xs) ++ ys)
  ≡⟨⟩
    suc (length (xs ++ ys))
  ≡⟨ cong suc (length-++ xs ys) ⟩
    suc (length xs + length ys)
  ≡⟨⟩
    length (x :: xs) + length ys
  ∎

-- Reverse
reverse : ∀ {A : Set} → List A → List A
reverse []        =  []
reverse (x :: xs)  =  reverse xs ++ [ x ]

{-
  Exercise reverse-++-distrib
-}
reverse-++-distrib : ∀ {A : Set} (xs ys : List A)
  → reverse (xs ++ ys) ≡ reverse ys ++ reverse xs
reverse-++-distrib [] ys = sym (++-identityʳ (reverse ys))
reverse-++-distrib (x :: xs) ys
  rewrite reverse-++-distrib xs ys
  | ++-assoc (reverse ys) (reverse xs) [ x ] = refl

{-
  Exercise reverse-involutive

  A function is an involution if when applied twice it acts as the identity function
-}
reverse-involutive : ∀ {A : Set} (xs : List A)
  → reverse (reverse xs) ≡ xs
reverse-involutive [] = refl
reverse-involutive (x :: xs) 
  rewrite reverse-++-distrib (reverse xs) [ x ]
  | reverse-involutive xs = refl

-- Faster Reverse
shunt : ∀ {A : Set} → List A → List A → List A
shunt []        ys  =  ys
shunt (x :: xs) ys  =  shunt xs (x :: ys)

shunt-reverse : ∀ {A : Set} (xs ys : List A)
  → shunt xs ys ≡ reverse xs ++ ys
shunt-reverse [] ys =
  begin
    shunt [] ys
  ≡⟨⟩
    ys
  ≡⟨⟩
    reverse [] ++ ys
  ∎
shunt-reverse (x :: xs) ys =
  begin
    shunt (x :: xs) ys
  ≡⟨⟩
    shunt xs (x :: ys)
  ≡⟨ shunt-reverse xs (x :: ys) ⟩
    reverse xs ++ (x :: ys)
  ≡⟨⟩
    reverse xs ++ ([ x ] ++ ys)
  ≡⟨ sym (++-assoc (reverse xs) [ x ] ys) ⟩
    (reverse xs ++ [ x ]) ++ ys
  ≡⟨⟩
    reverse (x :: xs) ++ ys
  ∎

reverse′ : ∀ {A : Set} → List A → List A
reverse′ xs = shunt xs []

reverses : ∀ {A : Set} (xs : List A)
  → reverse′ xs ≡ reverse xs
reverses xs =
  begin
    reverse′ xs
  ≡⟨⟩
    shunt xs []
  ≡⟨ shunt-reverse xs [] ⟩
    reverse xs ++ []
  ≡⟨ ++-identityʳ (reverse xs) ⟩
    reverse xs
  ∎

-- Map
map : ∀ {A B : Set} → (A → B) → List A → List B
map f []         =  []
map f (x :: xs)  =  f x :: map f xs

sucs : List ℕ → List ℕ
sucs = map suc

{-
  Exercise map-compose

  (map g ∘ map f) (x :: xs) ≡ map g (map f (x :: xs))
                            ≡ map g (f x :: map f xs)
                            ≡ g (f x) :: map g (map f xs)

-}
map-compose : ∀ {A B C : Set} (g : B → C) (f : A → B)
  → map (g ∘ f) ≡ map g ∘ map f
map-compose g = extensionality ∘ go g
  where
    go : ∀ {A B C : Set} (g : B → C) (f : A → B) (xs : List A)
      → map (g ∘ f) xs ≡ (map g ∘ map f) xs
    go g f []        = refl
    go g f (x :: xs) = 
      begin
        g (f x) :: map (g ∘ f) xs
      ≡⟨ cong (g (f x) ::_) (go g f xs) ⟩
        g (f x) :: (map g ∘ map f) xs
      ≡⟨⟩
        map g (map f (x :: xs))
      ≡⟨⟩
        (map g ∘ map f) (x :: xs)
      ∎

{-
  Exercise map-++-distribute
-}
map-++-distribute : ∀ {A B : Set} (f : A → B) (xs ys : List A)
  → map f (xs ++ ys) ≡ map f xs ++ map f ys
map-++-distribute f []        ys    = refl
map-++-distribute f (x :: xs) ys 
  rewrite map-++-distribute f xs ys = refl

{-
  Exercise map-Tree
-}
data Tree (A B : Set) : Set where
  leaf : A → Tree A B
  node : Tree A B → B → Tree A B → Tree A B

map-Tree : ∀ {A B C D : Set} → (A → C) → (B → D) → Tree A B → Tree C D
map-Tree f g (leaf a)            = leaf (f a)
map-Tree f g (node left b right) = node mapLeft (g b) mapRight
  where
    mapLeft  = map-Tree f g left
    mapRight = map-Tree f g right

-- Fold
foldr : ∀ {A B : Set} → (A → B → B) → B → List A → B
foldr _⊗_ e []        =  e
foldr _⊗_ e (x :: xs)  =  x ⊗ foldr _⊗_ e xs

sum : List ℕ → ℕ
sum = foldr _+_ 0

{-
  Exercise product
-}
product : List ℕ → ℕ
product = foldr _*_ 1

{-
  Exercise foldr-++
-}
foldr-++ : ∀ {A B : Set} (_⊗_ : A → B → B) (e : B) (xs ys : List A)
  → foldr _⊗_ e (xs ++ ys) ≡ foldr _⊗_ (foldr _⊗_ e ys) xs
foldr-++ _⊗_ e []        ys = refl
foldr-++ _⊗_ e (x :: xs) ys = cong (x ⊗_) (foldr-++ _⊗_ e xs ys)

{-
  Exercise foldr-::
-}
foldr-:: : ∀ {A : Set} (xs : List A)
  → foldr _::_ [] xs ≡ xs
foldr-:: []        = refl
foldr-:: (x :: xs) = cong (x ::_) (foldr-:: xs)

++-as-foldr : ∀ {A : Set} (xs ys : List A)
  → xs ++ ys ≡ foldr _::_ ys xs
++-as-foldr xs ys 
  rewrite sym (foldr-:: (xs ++ ys))
  | foldr-++ _::_ [] xs ys
  | foldr-:: ys = refl

{-
  Exercise map-is-foldr
-}
map-is-foldr : ∀ {A B : Set} (f : A → B)
  → map f ≡ foldr (λ x xs → f x :: xs) []
map-is-foldr = extensionality ∘ go
  where
    go : ∀ {A B : Set} (f : A → B) (xs : List A)
      → map f xs ≡ foldr (λ y ys → f y :: ys) [] xs
    go f []        = refl
    go f (x :: xs) = cong (f x ::_) (go f xs)

{-
  Exercise fold-Tree
-}
fold-Tree : ∀ {A B C : Set} → (A → C) → (C → B → C → C) → Tree A B → C
fold-Tree transformLeaf combine (leaf a)            = transformLeaf a
fold-Tree transformLeaf combine (node left b right) = combine reducedLeft b reducedRight
  where
    reducedLeft  = fold-Tree transformLeaf combine left
    reducedRight = fold-Tree transformLeaf combine right

{-
  Exercise map-is-fold-Tree
-}
map-is-fold-Tree : ∀ {A B C D : Set} (f : A → C) (g : B → D)
  → map-Tree f g ≡ fold-Tree (leaf ∘ f) (λ left b right → node left (g b) right)
map-is-fold-Tree f g = extensionality (go f g)
  where
    go : ∀ {A B C D : Set} (f : A → C) (g : B → D) (t : Tree A B)
      → map-Tree f g t ≡ fold-Tree (leaf ∘ f) (λ left b right → node left (g b) right) t
    go f g (leaf a) = refl
    go f g (node left b right) 
      rewrite go f g left | go f g right = refl

-- Monoids
record IsMonoid {A : Set} (_⊗_ : A → A → A) (e : A) : Set where
  field
    assoc : ∀ (x y z : A) → (x ⊗ y) ⊗ z ≡ x ⊗ (y ⊗ z)
    identityˡ : ∀ (x : A) → e ⊗ x ≡ x
    identityʳ : ∀ (x : A) → x ⊗ e ≡ x

open IsMonoid

-- Examples
+-monoid : IsMonoid _+_ 0
+-monoid =
  record
    { assoc = +-assoc
    ; identityˡ = +-identityˡ
    ; identityʳ = +-identityʳ
    }

*-monoid : IsMonoid _*_ 1
*-monoid =
  record
    { assoc = *-assoc
    ; identityˡ = *-identityˡ
    ; identityʳ = *-identityʳ
    }

++-monoid : ∀ {A : Set} → IsMonoid {List A} _++_ []
++-monoid =
  record
    { assoc = ++-assoc
    ; identityˡ = ++-identityˡ
    ; identityʳ = ++-identityʳ
    }


foldr-monoid : ∀ {A : Set} (_⊗_ : A → A → A) (e : A) → IsMonoid _⊗_ e →
  ∀ (xs : List A) (y : A) → foldr _⊗_ y xs ≡ (foldr _⊗_ e xs) ⊗ y
foldr-monoid _⊗_ e ⊗-monoid []        y = sym (identityˡ ⊗-monoid y)
foldr-monoid _⊗_ e ⊗-monoid (x :: xs) y
  rewrite foldr-monoid _⊗_ e ⊗-monoid xs y
  | assoc ⊗-monoid x (foldr _⊗_ e xs) y = refl

{-
  As a consequence of foldr-++, we can decompose fold over append in a monoid into two folds
-}
foldr-monoid-++ : ∀ {A : Set} (_⊗_ : A → A → A) (e : A) → IsMonoid _⊗_ e →
  ∀ (xs ys : List A) → foldr _⊗_ e (xs ++ ys) ≡ (foldr _⊗_ e xs) ⊗ (foldr _⊗_ e ys)
foldr-monoid-++ _⊗_ e ⊗-monoid xs ys
  rewrite foldr-++ _⊗_ e xs ys
  | foldr-monoid _⊗_ e ⊗-monoid xs (foldr _⊗_ e ys) = refl

{-
  Exercise foldl

  Define a function foldl which is analogous to foldr, but where operations associate to the left rather than the right
-}
foldl : ∀ {A B : Set} → (B → A → B) → B → List A → B
foldl _ e []        = e
foldl f e (x :: xs) = foldl f (f e x) xs

{-
  Exercise foldr-monoid-foldl

  Show that if _⊗_ and e form a monoid, then foldr _⊗_ e and foldl _⊗_ e always compute the same result
-}
foldl-monoid : ∀ {A : Set} (_⊗_ : A → A → A) (e : A) → IsMonoid _⊗_ e →
  ∀ (xs : List A) (y : A) → foldl _⊗_ y xs ≡ y ⊗ (foldl _⊗_ e xs)
foldl-monoid _⊗_ e ⊗-monoid []        y = sym (identityʳ ⊗-monoid y)
foldl-monoid _⊗_ e ⊗-monoid (x :: xs) y 
  rewrite identityˡ ⊗-monoid x 
  | foldl-monoid _⊗_ e ⊗-monoid xs (y ⊗ x) 
  | assoc ⊗-monoid y x (foldl _⊗_ e xs)
  | foldl-monoid _⊗_ e ⊗-monoid xs x = refl

foldr-monoid-foldl : ∀ {A : Set} 
  → (_⊗_ : A → A → A) → (e : A) → IsMonoid _⊗_ e
  → foldr _⊗_ e ≡ foldl _⊗_ e
foldr-monoid-foldl {A} _⊗_ e ⊗-monoid = extensionality go
  where
    go : (xs : List A) → foldr _⊗_ e xs ≡ foldl _⊗_ e xs
    go []        = refl
    go (x :: xs) 
      rewrite identityˡ ⊗-monoid x
      | go xs    = sym (foldl-monoid _⊗_ e ⊗-monoid xs x)

{-
  Exercise sum-downFrom

  TODO: Fix
-}
-- open import part1.Induction using 
--   ( zero-monus-n
--   ; *-distrib-+
--   )

-- downFrom : ℕ → List ℕ
-- downFrom zero     =  []
-- downFrom (suc n)  =  n :: downFrom n

-- 0∸n≡0 : ∀ (n : ℕ) → 0 ∸ n ≡ 0
-- 0∸n≡0 zero    = refl
-- 0∸n≡0 (suc _) = refl

-- n∸n≡0 : ∀ (n : ℕ)
--   → n ∸ n ≡ 0
-- n∸n≡0 zero    = refl
-- n∸n≡0 (suc n) = n∸n≡0 n
 

-- {-
--   Inductive case: Prove that

--   suc m * (n ∸ p)       ≡ suc m * n ∸ suc m * p
--   (n ∸ p) + m * (n ∸ p) ≡ (n + m * n) ∸ (p + m * p)

--   (n ∸ p) + m * (n ∸ p) ≡ (n ∸ p) + (m * n ∸ m * p) < I.H >
  
--   If n = 0:
--   (0 ∸ p) + (m * 0 ∸ m * p) ≡ (0 + m * 0) ∸ (p + m * p)
--   0 + (0 ∸ m * p)           ≡ 0 ∸ (p + m )

--   If n = suc x:
--   (suc x ∸ p) + (m * suc x ∸ m * p) ≡ (suc x + m * suc x) ∸ (p + m * p)
--   (suc x ∸ p) + (suc x * m ∸ m * p) ≡ (suc x + suc x * m) ∸ (p + m * p)
--                                     ≡ suc (x + suc x * m) ∸ (p + m * p)
--                                     ≡ suc (x + (x + x * m)) ∸ (p + m * p)
-- -}
-- *-distrib-∸ : ∀ (m n p : ℕ)
--   → m * (n ∸ p) ≡ m * n ∸ m * p
-- *-distrib-∸ zero    n p = refl
-- *-distrib-∸ (suc m) zero p
--   rewrite *-comm m 0 
--   | *-comm m (0 ∸ p)
--   | 0∸n≡0 p 
--   | 0∸n≡0 (p + m * p) = refl
-- *-distrib-∸ (suc m) (suc n) zero 
--   rewrite *-comm m 0  = refl
-- *-distrib-∸ (suc m) (suc n) (suc p)
--   rewrite *-distrib-∸ m n p
--   | *-comm m (suc n)
--   | *-comm m (suc p) = {!   !}

-- ∸-suc : ∀ (m n : ℕ)
--   → suc (m ∸ n) ≡ suc m ∸ n
-- ∸-suc zero zero = refl
-- ∸-suc zero (suc n) = {!   !}
-- ∸-suc (suc m) n = {!   !}

-- +-assoc-∸ : ∀ (m n p : ℕ)
--   → m + (n ∸ p) ≡ (m + n) ∸ p
-- +-assoc-∸ zero n p = refl
-- +-assoc-∸ (suc m) n p
--   rewrite +-assoc-∸ m n p = {!   !}


-- {-
--   Inductive case: Prove that 
  
--   sum (downFrom (suc n)) * 2 ≡ suc n * (suc n ∸ 1)
--   sum (n :: downFrom n) * 2  ≡ (suc n ∸ suc zero) + (n * (suc n ∸ suc zero))
--                              ≡ (n ∸ zero) + (n * (n ∸ zero))
--                              ≡ n + n * n

--   sum (n :: downFrom n) * 2 ≡ (n + sum (downFrom n)) * 2
--                             ≡ n * 2 + sum (downFrom n) * 2
--                             ≡ n * 2 + n * (n ∸ 1) < I.H >
--                             ≡ n + n + n * (n ∸ 1)
--                             ≡ n + n + (n * n ∸ n)
-- -}
-- sum-downFrom : ∀ (n : ℕ)
--   → sum (downFrom n) * 2 ≡ n * (n ∸ 1)
-- sum-downFrom zero = refl
-- sum-downFrom (suc n) = 
--   begin
--     sum (n :: downFrom n) * 2
--   ≡⟨⟩
--     (n + sum (downFrom n)) * 2
--   ≡⟨ *-distrib-+ n (sum (downFrom n)) 2 ⟩ 
--     n * 2 + sum (downFrom n) * 2
--   ≡⟨ cong (n * 2 +_) (sum-downFrom n) ⟩
--     n * 2 + n * (n ∸ 1)
--   ≡⟨ cong (_+ n * (n ∸ 1)) (*-comm n 2) ⟩
--     2 * n + n * (n ∸ 1)
--   ≡⟨⟩
--     n + 1 * n + n * (n ∸ 1)
--   ≡⟨ cong (λ m → n + m + n * (n ∸ 1)) (*-identityˡ n) ⟩
--     n + n + n * (n ∸ 1)
--   ≡⟨ cong (n + n +_) (*-distrib-∸ n n 1) ⟩
--     n + n + (n * n ∸ n * 1)
--   ≡⟨ cong (λ m → n + n + (n * n ∸ m)) (*-identityʳ n) ⟩ 
--     n + n + (n * n ∸ n)
--   ≡⟨ +-assoc n n (n * n ∸ n) ⟩ 
--     n + (n + (n * n ∸ n))
--   ≡⟨ cong (n +_) (+-assoc-∸ n (n * n) n) ⟩ 
--     n + ((n + n * n) ∸ n)
--   ≡⟨ +-assoc-∸ n (n + n * n) n ⟩ 
--     (n + (n + n * n)) ∸ n
--   ≡⟨ cong (_∸ n) (+-comm n (n + n * n)) ⟩ 
--     (n + n * n + n) ∸ n
--   ≡⟨ sym (+-assoc-∸ (n + n * n) n n ) ⟩ 
--     n + n * n + (n ∸ n)
--   ≡⟨ cong (n + n * n +_) (n∸n≡0 n) ⟩ 
--     n + n * n + 0
--   ≡⟨ +-identityʳ (n + n * n) ⟩ 
--     n + n * n
--   ∎