module part1.Negation where

open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; cong)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (_×_)
open import part1.Isomorphism using (_≃_; extensionality)

{-
  Negation

  Given a proposition A, the negation ¬ A holds if A cannot hold.

  ¬ A holds, if assuming A leads to ⊥ (absurdity)

  Given the evidence that ¬ A and A hold, then we have the 
  evidence that ⊥ holds, which is a contradiction
-}
¬_ : Set → Set
¬ A = A → ⊥

infix 3 ¬_

¬-elim : ∀ {A : Set}
  → ¬ A
  → A
    ---
  → ⊥
¬-elim ¬a a = ¬a a

{-
  In classical logic we have that ¬ ¬ A ⇔ A. Agda uses intuitionistic logic,
  where we only have have A → ¬ ¬ A
-}
¬¬-intro : ∀ {A : Set}
  → A
    -----
  → ¬ ¬ A
¬¬-intro a = λ ¬a → ¬a a

¬¬-intro′ : ∀ {A : Set}
  → A
    -----
  → ¬ ¬ A
¬¬-intro′ x ¬x = ¬x x

{-
  We cannot show that ¬ ¬ A → A, but we can show that ¬ ¬ ¬ A → ¬ A

  ¬ (¬ ¬ A) = ¬ ¬ A → ⊥
-}
¬¬¬-elim : ∀ {A : Set}
  → ¬ ¬ ¬ A
    -------
  → ¬ A
¬¬¬-elim ¬¬¬a = λ a → ¬¬¬a (¬¬-intro a)

contraposition : ∀ {A B : Set}
  → (A → B)
    -----------
  → (¬ B → ¬ A)
contraposition f ¬b a = ¬b (f a)

-- Inequality
_≢_ : ∀ {A : Set} → A → A → Set
x ≢ y  =  ¬ (x ≡ y)

_ : 1 ≢ 2
_ = λ() 

-- Peano's postulate: zero is not the successor of any number
peano : ∀ {m : ℕ} → zero ≢ suc m
peano = λ()

{-
  We can view as raising to the zero power. This also corresponds
  to what we know in arithmetic

    0 ^ n  ≡  1,  if n ≡ 0
           ≡  0,  if n ≢ 0
-}
id : ⊥ → ⊥
id x = x

id′ : ⊥ → ⊥
id′ ()

id≡id′ : id ≡ id′
id≡id′ = extensionality (λ())

assimilation : ∀ {A : Set} (¬x ¬x′ : ¬ A) → ¬x ≡ ¬x′
assimilation ¬x ¬x′ = extensionality (λ x → ⊥-elim (¬x x))

{-
  Exercise <-irreflexive

  Using negation, show that strict inequality is irreflexive, that is, n < n holds for no n.

-}
open import part1.Relations using (_<_)
open _<_

<-irreflexive : ∀ {n : ℕ}
  → ¬ (n < n)
<-irreflexive (s<s n<n) = <-irreflexive n<n

{-
  Exercise trichotomy
-}
data Trichotomy (m n : ℕ) : Set where

  less : 
      m < n
    → ¬ (m ≡ n)
    → ¬ (n < m)
      --------------
    → Trichotomy m n

  equal :
      m ≡ n
    → ¬ (m < n)
    → ¬ (n < m)
      --------------
    → Trichotomy m n

  greater :
      n < m
    → ¬ (m ≡ n)
    → ¬ (m < n)
      --------------
    → Trichotomy m n

¬n<zero : ∀ {n : ℕ} → ¬ (n < zero)
¬n<zero ()

≢-sym : ∀ {A : Set} {x y : A}
  → x ≢ y
    -----
  → y ≢ x
≢-sym x≢y y≡x = x≢y (sym y≡x)

≢-suc : ∀ {m n : ℕ}
  → m ≢ n
    -------------
  → suc m ≢ suc n
≢-suc m≢m refl = ¬-elim m≢m refl

¬s<s : ∀ {m n : ℕ}
  → ¬ (m < n)
    ----------------
  → ¬ (suc m < suc n)
¬s<s ¬m<n (s<s m<n) = ¬-elim ¬m<n m<n

<-trichotomy : ∀ {m n : ℕ} → Trichotomy m n
<-trichotomy {zero} {zero}  = equal refl <-irreflexive <-irreflexive
<-trichotomy {zero} {suc n} = less z<s peano ¬n<zero
<-trichotomy {suc m} {zero} = greater z<s (≢-sym peano) ¬n<zero
<-trichotomy {suc m} {suc n} 
    with <-trichotomy {m} {n}
... | less m<n m≢n ¬n<m    = less (s<s m<n) (≢-suc m≢n) (¬s<s ¬n<m)
... | equal m≡n ¬m<n ¬n<m  = equal (cong suc m≡n) (¬s<s ¬m<n) (¬s<s ¬n<m)
... | greater n<m m≢n ¬m<n = greater (s<s n<m) (≢-suc m≢n) (¬s<s ¬m<n)