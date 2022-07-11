module part1.Negation where

open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; cong)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Empty using (⊥; ⊥-elim)
-- open import Data.Sum using (_⊎_; inj₁; inj₂)
-- open import Data.Product using (_×_)
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

{-
  Exercise ⊎-dual-×

  ¬ (A ⊎ B) ≃ (¬ A) × (¬ B)

  (Version of De Morgan's Law)
-}
open import part1.Connectives using 
  ( _⊎_
  ; inj₁; inj₂
  ; _×_; ⟨_,_⟩
  ; →-distrib-⊎; ⊎-comm; case-⊎
  )
open part1.Isomorphism.≃-Reasoning

⊎-dual-× : ∀ {A B : Set}
  → ¬ (A ⊎ B) ≃ (¬ A) × (¬ B)
⊎-dual-× {A} {B} = →-distrib-⊎ {A} {B} {⊥}

{-
  We cannot have ¬ (A × B) ≃ (¬ A) ⊎ (¬ B)
  since there is no function of type ¬ (A × B) → (¬ A) ⊎ (¬ B),
  but we can have the converse version
-}
x-weak-⊎ : ∀ {A B : Set}
  → (¬ A) ⊎ (¬ B) → ¬ (A × B) 
x-weak-⊎ (inj₁ ¬a) ⟨ a , _ ⟩ = ¬a a
x-weak-⊎ (inj₂ ¬b) ⟨ _ , b ⟩ = ¬b b

{-
  Excluded middle is irrefutable

  The law of the excluded middle does not hold in intuitionistic logic. However, we can show that it is irrefutable, 
  meaning that the negation of its negation is provable (and hence that its negation is never provable)
-}
postulate
  em : ∀ {A : Set} → A ⊎ ¬ A

em-irrefutable : ∀ {A : Set} → ¬ ¬ (A ⊎ ¬ A)
em-irrefutable ¬em = ¬em (inj₂ λ{ a → ¬em (inj₁ a) })

{-
  Exercise Classical
-}
open import Function using (_∘_)

postulate
  ¬-double-elim : ∀ {A : Set}   → ¬ ¬ A → A
  pierce-law    : ∀ {A B : Set} → ((A → B) → A) → A
  impl-disjunction : ∀ {A B : Set} → (A → B) → ¬ A ⊎ B
  de-morgan     : ∀ {A B : Set} → ¬ (¬ A × ¬ B) → A ⊎ B

-- Excluded middle implies all others
em→¬-double-elim :  
    (∀ {A : Set} → A ⊎ ¬ A)
    -------------------------
  → ∀ {A : Set} → ¬ ¬ A → A
em→¬-double-elim a⊎¬a ¬¬a 
    with a⊎¬a 
... | inj₁ a  = a
... | inj₂ ¬a = ⊥-elim (¬¬a ¬a)

em→pierce-law : 
    (∀ {A : Set} → A ⊎ ¬ A)
    -----------------
  → ∀ {A B : Set} → ((A → B) → A) → A
em→pierce-law a⊎¬a f 
    with a⊎¬a
... | inj₁ a  = a
... | inj₂ ¬a = f λ{a → ⊥-elim (¬a a)}

em→impl-disjunction :
    (∀ {A : Set} → A ⊎ ¬ A)
    -----------------
  → ∀ {A B : Set} → (A → B) → ¬ A ⊎ B
em→impl-disjunction a⊎¬a f 
    with a⊎¬a
... | inj₁ a  = inj₂ (f a)
... | inj₂ ¬a = inj₁ ¬a

em→de-morgan : 
    (∀ {A : Set} → A ⊎ ¬ A)
    ---------------------
  → ∀ {A B : Set} → ¬ (¬ A × ¬ B) → A ⊎ B
em→de-morgan x⊎¬x f
    with ⟨ x⊎¬x , x⊎¬x ⟩
... | ⟨ inj₁ a , _ ⟩        = inj₁ a
... | ⟨ _ , inj₁ b ⟩        = inj₂ b
... | ⟨ inj₂ ¬a , inj₂ ¬b ⟩ = ⊥-elim (f ⟨ ¬a , ¬b ⟩)

-- Double negation implies all others
¬-double-elim→em : 
    (∀ {A : Set} → ¬ ¬ A → A)
    -------------------------
  → ∀ {A : Set} → A ⊎ ¬ A
¬-double-elim→em ¬¬-elim = ¬¬-elim λ
  { 
    ¬_a⊎¬a → ¬_a⊎¬a (inj₂ λ{ a → ¬_a⊎¬a (inj₁ a) }) 
  }

¬-double-elim→pierce-law :
    (∀ {A : Set} → ¬ ¬ A → A)
    ---------------------------------
  → ∀ {A B : Set} → ((A → B) → A) → A
¬-double-elim→pierce-law ¬¬-elim f = ¬¬-elim λ
  { 
    ¬a → ⊥-elim (¬a (f λ{ a → ⊥-elim (¬a a) })) 
  }

¬-double-elim→impl-disjunction : 
    (∀ {A : Set} → ¬ ¬ A → A)
    ---------------------------------
  → ∀ {A B : Set} → (A → B) → ¬ A ⊎ B
¬-double-elim→impl-disjunction ¬¬-elim f = ¬¬-elim λ
  { 
    ¬_¬a⊎b → ¬_¬a⊎b (inj₁ λ{ a → ¬_¬a⊎b (inj₂ (f a)) }) 
  }

¬-double-elim→de-morgan : 
    (∀ {A : Set} → ¬ ¬ A → A)
    -------------------------------------
  → ∀ {A B : Set} → ¬ (¬ A × ¬ B) → A ⊎ B
¬-double-elim→de-morgan ¬¬-elim ¬_¬a×¬b = ¬¬-elim λ
  { 
    ¬_a⊎b → ¬_¬a×¬b ⟨ ( λ a → ¬_a⊎b (inj₁ a) ) , ( λ b → ¬_a⊎b (inj₂ b) ) ⟩ 
  }

-- Pierce law implies all others
pierce-law→em :
    (∀ {A B : Set} → ((A → B) → A) → A)
    -----------------------------------
  → ∀ {A : Set} → A ⊎ ¬ A
pierce-law→em pierce = pierce λ{ ¬em → ⊥-elim (em-irrefutable ¬em) }

pierce-law→¬-double-elim : ∀ {A B : Set}
  → (∀ {A B : Set} → ((A → B) → A) → A)
    -----------------------------------
  → ∀ {A : Set} → ¬ ¬ A → A
pierce-law→¬-double-elim pierce ¬¬a = pierce λ{ ¬a → ⊥-elim (¬¬a ¬a) }

pierce-law→impl-disjunction :
    (∀ {A B : Set} → ((A → B) → A) → A)
    -----------------------------------
  → ∀ {A B : Set} → (A → B) → ¬ A ⊎ B
pierce-law→impl-disjunction pierce f = pierce λ
  { 
    ¬_¬a⊎b →  inj₁ λ{ a → ¬_¬a⊎b (inj₂ (f a)) } 
  }

pierce-law→de-morgan :
    (∀ {A B : Set} → ((A → B) → A) → A)
    -------------------------------------
  → ∀ {A B : Set} → ¬ (¬ A × ¬ B) → A ⊎ B
pierce-law→de-morgan pierce ¬_¬a×¬b = pierce λ
  {
    ¬_a⊎b → ⊥-elim (¬_¬a×¬b ⟨ ( λ a → ¬_a⊎b (inj₁ a) ) , ( λ b → ¬_a⊎b (inj₂ b) ) ⟩)
  }

-- Implication as disjunction implies all others
impl-disjunction→em : 
    (∀ {A B : Set} → (A → B) → ¬ A ⊎ B)
    -----------------------------------
  → ∀ {A : Set} → A ⊎ ¬ A
impl-disjunction→em disj = _≃_.to ⊎-comm (disj λ{ a → a })

impl-disjunction→¬-double-elim : 
    (∀ {A B : Set} → (A → B) → ¬ A ⊎ B)
    -----------------------------------
  → ∀ {A : Set} → ¬ ¬ A → A
impl-disjunction→¬-double-elim = em→¬-double-elim ∘ impl-disjunction→em

impl-disjunction→pierce-law : 
    (∀ {A B : Set} → (A → B) → ¬ A ⊎ B)
    -----------------------------------
  → ∀ {A B : Set} → ((A → B) → A) → A
impl-disjunction→pierce-law = em→pierce-law ∘ impl-disjunction→em

impl-disjunction→de-morgan : 
    (∀ {A B : Set} → (A → B) → ¬ A ⊎ B)
    -----------------------------------
  → ∀ {A B : Set} → ¬ (¬ A × ¬ B) → A ⊎ B
impl-disjunction→de-morgan = em→de-morgan ∘ impl-disjunction→em
