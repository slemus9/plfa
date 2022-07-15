module part1.Lists where 

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; sym; trans; cong)
open Eq.≡-Reasoning
open import Data.Bool using (Bool; true; false; T; _∧_; _∨_; not)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _∸_; _≤_; s≤s; z≤n)
open import Data.Nat.Properties using
  (+-assoc; +-identityˡ; +-identityʳ; *-assoc; *-identityˡ; *-identityʳ)
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Data.Product using (_×_; ∃; ∃-syntax) renaming (_,_ to ⟨_,_⟩)
open import Function using (_∘_)
open import Level using (Level)
open import part1.Isomorphism using (_≃_; _⇔_)

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