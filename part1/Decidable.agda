module part1.Decidable where

{-
  Decidable

  We have a choice as to how to represent relations: 
    - as an inductive data type of evidence that the relation holds
    - as a function that computes whether the relation holds
-}
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)
open Eq.≡-Reasoning
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (_×_) renaming (_,_ to ⟨_,_⟩)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Nullary using (¬_)
open import Relation.Nullary.Negation using ()
  renaming (contradiction to ¬¬-intro)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥; ⊥-elim)
open import part1.Relations using (_<_; z<s; s<s; _≤_)
open import part1.Isomorphism using (_⇔_)
open import Function using (_∘_; const)

open _≤_

-- Evidence
2≤4 : 2 ≤ 4
2≤4 = s≤s (s≤s z≤n)

¬4≤2 : ¬ (4 ≤ 2)
¬4≤2 (s≤s (s≤s ()))

-- Computation
data Bool : Set where
  true  : Bool
  false : Bool

infix 4 _≤ᵇ_

_≤ᵇ_ : ℕ → ℕ → Bool
zero ≤ᵇ n       =  true
suc m ≤ᵇ zero   =  false
suc m ≤ᵇ suc n  =  m ≤ᵇ n

_ : (2 ≤ᵇ 4) ≡ true
_ =
  begin
    2 ≤ᵇ 4
  ≡⟨⟩
    1 ≤ᵇ 3
  ≡⟨⟩
    0 ≤ᵇ 2
  ≡⟨⟩
    true
  ∎

_ : (4 ≤ᵇ 2) ≡ false
_ =
  begin
    4 ≤ᵇ 2
  ≡⟨⟩
    3 ≤ᵇ 1
  ≡⟨⟩
    2 ≤ᵇ 0
  ≡⟨⟩
    false
  ∎

-- Relating Evidence to Computation
T : Bool → Set
T true   =  ⊤
T false  =  ⊥

-- T b is only inhabited when b ≡ true
T→≡ : ∀ (b : Bool) → T b → b ≡ true
T→≡ true tt   =  refl
T→≡ false ()

≡→T : ∀ {b : Bool} → b ≡ true → T b
≡→T refl  =  tt

≤ᵇ→≤ : ∀ (m n : ℕ) → T (m ≤ᵇ n) → m ≤ n
≤ᵇ→≤ zero n b          = z≤n
≤ᵇ→≤ (suc m) (suc n) b = s≤s (≤ᵇ→≤ m n b)

≤→≤ᵇ : ∀ {m n : ℕ} → m ≤ n → T (m ≤ᵇ n)
≤→≤ᵇ z≤n        =  tt
≤→≤ᵇ (s≤s m≤n)  =  ≤→≤ᵇ m≤n

-- Best of both worlds: Decidable
data Dec (A : Set) : Set where
  yes :   A → Dec A
  no  : ¬ A → Dec A

¬s≤z : ∀ {m : ℕ} → ¬ (suc m ≤ zero)
¬s≤z ()

¬s≤s : ∀ {m n : ℕ} → ¬ (m ≤ n) → ¬ (suc m ≤ suc n)
¬s≤s ¬m≤n (s≤s m≤n) = ¬m≤n m≤n

_≤?_ : ∀ (m n : ℕ) → Dec (m ≤ n)
zero  ≤? n                   =  yes z≤n
suc m ≤? zero                =  no ¬s≤z
suc m ≤? suc n with m ≤? n
...               | yes m≤n  =  yes (s≤s m≤n)
...               | no ¬m≤n  =  no (¬s≤s ¬m≤n)

_ : 2 ≤? 4 ≡ yes (s≤s (s≤s z≤n))
_ = refl

_ : 4 ≤? 2 ≡ no (¬s≤s (¬s≤s ¬s≤z))
_ = refl

{-
  Exercise _<?_
-}
¬n<z : ∀ {n : ℕ} → ¬ (n < zero)
¬n<z ()

¬s<s : ∀ {m n : ℕ} 
  → ¬ (m < n)
    -----------------
  → ¬ (suc m < suc n) 
¬s<s ¬m<n (s<s m<n) = ¬m<n m<n

_<?_ : ∀ (m n : ℕ) → Dec (m < n)
zero <? zero   = no ¬n<z
zero <? suc n  = yes z<s
suc m <? zero  = no ¬n<z
suc m <? suc n 
    with m <? n
... | yes m<n = yes (s<s m<n)
... | no ¬m<n = no (¬s<s ¬m<n)

{-
  Exercise _≡ℕ?_
-}
¬≡-suc : ∀ {m n : ℕ}
  → ¬ (m ≡ n)
    -----------------
  → ¬ (suc m ≡ suc n)
¬≡-suc ¬m≡m refl = ¬m≡m refl

_≡ℕ?_ : ∀ (m n : ℕ) → Dec (m ≡ n)
zero ≡ℕ? zero = yes refl
zero ≡ℕ? suc n = no λ()
suc m ≡ℕ? zero = no λ()
suc m ≡ℕ? suc n 
    with m ≡ℕ? n
... | yes refl = yes refl
... | no ¬m≡n  = no (¬≡-suc ¬m≡n)

-- Decidables from booleans, and booleans from decidables
_≤?′_ : ∀ (m n : ℕ) → Dec (m ≤ n)
m ≤?′ n with m ≤ᵇ n | ≤ᵇ→≤ m n | ≤→≤ᵇ {m} {n}
...        | true   | p        | _            = yes (p tt)
...        | false  | _        | ¬p           = no ¬p

-- Erasure
⌊_⌋ : ∀ {A : Set} → Dec A → Bool
⌊ yes x ⌋  =  true
⌊ no ¬x ⌋  =  false

_≤ᵇ′_ : ℕ → ℕ → Bool
m ≤ᵇ′ n  =  ⌊ m ≤? n ⌋

toWitness : ∀ {A : Set} {D : Dec A} → T ⌊ D ⌋ → A
toWitness {A} {yes x} tt  =  x
toWitness {A} {no ¬x} ()

fromWitness : ∀ {A : Set} {D : Dec A} → A → T ⌊ D ⌋
fromWitness {A} {yes x} _  =  tt
fromWitness {A} {no ¬x} x  =  ¬x x

≤ᵇ′→≤ : ∀ {m n : ℕ} → T (m ≤ᵇ′ n) → m ≤ n
≤ᵇ′→≤  =  toWitness

≤→≤ᵇ′ : ∀ {m n : ℕ} → m ≤ n → T (m ≤ᵇ′ n)
≤→≤ᵇ′  =  fromWitness

-- Logical connectives

-- Conjunction
infixr 6 _∧_

_∧_ : Bool → Bool → Bool
true  ∧ true  = true
_     ∧ _     = false

infixr 6 _×-dec_

_×-dec_ : ∀ {A B : Set} → Dec A → Dec B → Dec (A × B)
yes a ×-dec yes b = yes ⟨ a , b ⟩
no ¬a ×-dec _     = no λ{ ⟨ a , b ⟩ → ¬a a }
_     ×-dec no ¬b = no λ{ ⟨ a , b ⟩ → ¬b b }

-- Disjunction
infixr 5 _∨_

_∨_ : Bool → Bool → Bool
false ∨ false  = false
_     ∨ _      = true 

infixr 5 _⊎-dec_

_⊎-dec_ : ∀ {A B : Set} → Dec A → Dec B → Dec (A ⊎ B)
yes a ⊎-dec _     = yes (inj₁ a)
_     ⊎-dec yes b = yes (inj₂ b)
no ¬a ⊎-dec no ¬b = no λ{ (inj₁ a) → ¬a a ; (inj₂ b) → ¬b b }

not : Bool → Bool
not true  = false
not false = true

¬? : ∀ {A : Set} → Dec A → Dec (¬ A)
¬? (yes x)  =  no (¬¬-intro x)
¬? (no ¬x)  =  yes ¬x

-- Connective that corresponds to implication
_⊃_ : Bool → Bool → Bool
_     ⊃ true   =  true
false ⊃ _      =  true
true  ⊃ false  =  false

_→-dec_ : ∀ {A B : Set} → Dec A → Dec B → Dec (A → B)
_     →-dec yes y  =  yes (λ _ → y)
no ¬x →-dec _      =  yes (λ x → ⊥-elim (¬x x))
yes x →-dec no ¬y  =  no (λ f → ¬y (f x))

{-
  Exercise erasure
-}
∧-× : ∀ {A B : Set} (x : Dec A) (y : Dec B) → ⌊ x ⌋ ∧ ⌊ y ⌋ ≡ ⌊ x ×-dec y ⌋
∧-× (yes _) (yes _) = refl
∧-× (yes _) (no _)  = refl
∧-× (no _)  (yes _) = refl
∧-× (no _)  (no _)  = refl

∨-⊎ : ∀ {A B : Set} (x : Dec A) (y : Dec B) → ⌊ x ⌋ ∨ ⌊ y ⌋ ≡ ⌊ x ⊎-dec y ⌋
∨-⊎ (yes _) (yes _) = refl
∨-⊎ (yes _) (no _)  = refl
∨-⊎ (no _)  (yes _) = refl
∨-⊎ (no _)  (no _)  = refl

not-¬ : ∀ {A : Set} (x : Dec A) → not ⌊ x ⌋ ≡ ⌊ ¬? x ⌋
not-¬ (yes _) = refl
not-¬ (no _)  = refl

{-
  Exercise iff-erasure
-}
open _⇔_

_iff_ : Bool → Bool → Bool
true  iff true  = true
false iff false = true
_     iff _     = false

_⇔-dec_ : ∀ {A B : Set} → Dec A → Dec B → Dec (A ⇔ B)
yes a ⇔-dec yes b = yes (record { to = const b ; from = const a })
yes a ⇔-dec no ¬b = no λ a⇔b → ¬b (to a⇔b a)
no ¬a ⇔-dec yes b = no λ a⇔b → ¬a (from a⇔b b)
no ¬a ⇔-dec no ¬b = yes (record { to = ⊥-elim ∘ ¬a ; from = ⊥-elim ∘ ¬b })


iff-⇔ : ∀ {A B : Set} (x : Dec A) (y : Dec B) → ⌊ x ⌋ iff ⌊ y ⌋ ≡ ⌊ x ⇔-dec y ⌋
iff-⇔ (yes _) (yes _) = refl
iff-⇔ (yes _) (no _)  = refl
iff-⇔ (no _)  (yes _) = refl
iff-⇔ (no _)  (no _)  = refl

-- Proof by reflection
minus : (m n : ℕ) (n≤m : n ≤ m) → ℕ
minus m       zero    _         = m
minus (suc m) (suc n) (s≤s n≤m) = minus m n n≤m

-- it is painful to use, since we have to explicitly provide the proof that n ≤ m
_ : minus 5 3 (s≤s (s≤s (s≤s z≤n))) ≡ 2
_ = refl

{-
  Use the Dec data type

  Use the implicit type T ⌊ n ≤? m ⌋, which does the following:

  1. run the decision procedure n ≤? m. This provides the evidence of whether n ≤ m holds or not
  2. erase the evidence to a boolean using ⌊ ⌋
  3. apply T to map the booleans to the world of evidence

  An implicit argument of this type works as a guard

  We can safely use _-_ as long as we statically know the two numbers
-}
_-_ : (m n : ℕ) {n≤m : T ⌊ n ≤? m ⌋} → ℕ
_-_ m n {n≤m} = minus m n (toWitness n≤m)

True : ∀ {Q} → Dec Q → Set
True Q = T ⌊ Q ⌋

{-
  Exercise False
-}
F : Bool → Set
F true  = ⊥
F false = ⊤

False : ∀ {Q} → Dec Q → Set
False Q = F ⌊ Q ⌋

toWitnessFalse : ∀ {A : Set} {D : Dec A} → False D → ¬ A
toWitnessFalse {A} {yes a} ()
toWitnessFalse {A} {no ¬a} tt = ¬a

fromWitnessFalse : ∀ {A : Set} {D : Dec A} → ¬ A → False D
fromWitnessFalse {A} {yes a} ¬a = ¬a a
fromWitnessFalse {A} {no ¬a} _  = tt

{-
  Standard Library

  import Data.Bool.Base using (Bool; true; false; T; _∧_; _∨_; not)
  import Data.Nat using (_≤?_)
  import Relation.Nullary using (Dec; yes; no)
  import Relation.Nullary.Decidable using (⌊_⌋; True; toWitness; fromWitness)
  import Relation.Nullary.Negation using (¬?)
  import Relation.Nullary.Product using (_×-dec_)
  import Relation.Nullary.Sum using (_⊎-dec_)
  import Relation.Binary using (Decidable)
-}