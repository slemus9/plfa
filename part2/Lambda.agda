module part2.Lambda where

open import Data.Bool using (Bool; true; false; T; not)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using (List; _∷_; [])
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (∃-syntax; _×_)
open import Data.String using (String; _≟_)
open import Data.Unit using (tt)
open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Relation.Nullary.Decidable using (False; toWitnessFalse)
open import Relation.Nullary.Negation using (¬?)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl)

{-
  Syntax of terms

  L, M, N  ::=
    ` x  |  ƛ x ⇒ N  |  L · M  |                         # Lambda calculus
    `zero  |  `suc M  |  case L [zero⇒ M |suc x ⇒ N ]  | # Naturals
    μ x ⇒ M                                              # Fixpoint. For recursion
-}
Id : Set
Id = String

infix 5 ƛ_⇒_
infix 5 μ_⇒_
infixl 7 _·_
infix 8 `suc_
infix 9 `_

data Term : Set where
  -- Core lambda calculus
  `_                   : Id → Term          -- Variables
  ƛ_⇒_                 : Id → Term → Term   -- Abstractions
  _·_                  : Term → Term → Term -- Applications
  -- Natural numbers
  `zero                : Term                           -- Zero
  `suc_                : Term → Term                    -- Succesor
  case_[zero⇒_|suc_⇒_] : Term → Term → Id → Term → Term -- Case
  -- Recursion
  μ_⇒_                 : Id → Term → Term -- Fixpoint

-- Examples
two : Term
two = `suc `suc `zero

plus : Term
plus = μ "+" ⇒ ƛ "m" ⇒ ƛ "n" ⇒
  case ` "m" 
    [zero⇒     ` "n"
    |suc "m" ⇒ `suc (` "+" · ` "m" · ` "n")
    ]

{-
  Church numerals
  The number n is represented by a function that accepts two arguments and applies the
  first one, n times to the second one

  ChurchNat : (a -> a) -> a -> a

  zero s z = z

  one s z = s z

  two s z = s (s z)

  three s z = s (s (s z))

  n s z = s (s .. (s z))

  suc : ChurchNat -> ChurchNat
  suc n = \ s z -> s (n s z)

  plus : ChurchNat -> ChurchNat -> ChurchNat
  plus m n = \ s -> m s . n s

  mul : ChurchNat -> ChurchNat -> ChurchNat
  mul m n = \ s -> m (n s) z
-}
twoᶜ : Term
twoᶜ = ƛ "s" ⇒ ƛ "z" ⇒ ` "s" · (` "s" · ` "z")

plusᶜ : Term
plusᶜ = ƛ "m" ⇒ ƛ "n" ⇒ ƛ "s" ⇒ ƛ "z" ⇒
  ` "m" · ` "s" · (` "n" · ` "s" · ` "z")

sucᶜ : Term
sucᶜ = ƛ "n" ⇒ `suc (` "n")

-- Exercise mul
mul : Term
mul = μ "*" ⇒ ƛ "m" ⇒ ƛ "n" ⇒ 
  case ` "m"
    [zero⇒     `zero
    |suc "m" ⇒ plus · ` "n" · (` "*" · ` "m" · ` "n")
    ]

-- Exercise mulᶜ
mulᶜ : Term
mulᶜ = ƛ "m" ⇒ ƛ "n" ⇒ ƛ "s" ⇒ ƛ "z" ⇒ 
  ` "m" · (` "n" · ` "s") · ` "z"

-- Exercise primed
var? : (t : Term) → Bool
var? (` _) = true
var? _     = false

ƛ'_⇒_ : (t : Term) → {_ : T (var? t)} → Term → Term
ƛ' (` x) ⇒ N = ƛ x ⇒ N

case'_[zero⇒_|suc_⇒_] : Term → Term → (t : Term) → {_ : T (var? t)} → Term → Term
case' L [zero⇒ M |suc (` x) ⇒ N ] = case L [zero⇒ M |suc x ⇒ N ]

μ'_⇒_ : (t : Term) → {_ : T (var? t)} → Term → Term
μ' (` x) ⇒ N  =  μ x ⇒ N

{-
  Using T, we ensure that we can only use the primed function when we have an 
  implicit evidence that the required term is a variable. For example, the 
  following is not possible:

  _ : Term
  _ = ƛ' two ⇒ two
-}
plus' : Term
plus' = μ' + ⇒ ƛ' m ⇒ ƛ' n ⇒
  case' m
    [zero⇒ n
    |suc m ⇒ `suc (+ · m · n) ]
  where
  +  =  ` "+"
  m  =  ` "m"
  n  =  ` "n"

mul' : Term
mul' = μ' * ⇒ ƛ' m ⇒ ƛ' n ⇒ 
  case' m
    [zero⇒ `zero
    |suc m ⇒ plus' · n · (* · m · n)
    ]
  where
  * = ` "*"
  m = ` "m"
  n = ` "n"

{-
  Values

  A value is a term that corresponds to an answer

  suc `suc `suc `suc `zero is a value while plus · two · two is not. 
  
  All function abstractions are also values (for example, plus)
-}
data Value : Term → Set where

  V-ƛ : ∀ {x N}
      ---------------
    → Value (ƛ x ⇒ N)

  V-zero :
      -----------
      Value `zero

  V-suc : ∀ {V}
    → Value V
      --------------
    → Value (`suc V)

{-
  Substitution

  N [ x := V ] - "substitute the term V for free occurences of variable x in the term N"

  Substitution works if V is a closed term (has no free variables)

  (ƛ "z" ⇒ ` "s" · (` "s" · ` "z")) [ "s" := sucᶜ ] yields ƛ "z" ⇒ sucᶜ · (sucᶜ · ` "z")
  (ƛ "x" ⇒ ` "y") [ "y" := `zero ] yields ƛ "x" ⇒ `zero
  (ƛ "x" ⇒ ` "x") [ "x" := `zero ] yields ƛ "x" ⇒ ` "x"
  (ƛ "y" ⇒ ` "y") [ "x" := `zero ] yields ƛ "y" ⇒ ` "y"

  Substitution with terms that are not closed is possible, but there should be a suitable
  remaining of variables
-}
infix 9 _[_:=_]

_[_:=_] : Term → Id → Term → Term

(` x) [ y := V ] with x ≟ y
... | yes _ = V
... | no  _ = ` x

f @ (ƛ x ⇒ N) [ y := V ] with x ≟ y
... | yes _ = f
... | no  _ = ƛ x ⇒ N [ y := V ]

(L · M) [ y := V ] = L [ y := V ] · M [ y := V ]

(`zero) [ y := V ] = `zero

(`suc M) [ y := V ] = `suc (M [ y := V ])

(case L [zero⇒ M |suc x ⇒ N ]) [ y := V ] with x ≟ y
... | yes _ = case (L [ y := V ])
  [zero⇒   M [ y := V ]
  |suc x ⇒ N
  ]
... | no  _ = case (L [ y := V ])
  [zero⇒   M [ y := V ]
  |suc x ⇒ N [ y := V ]
  ]

f @ (μ x ⇒ N) [ y := V ] with x ≟ y
... | yes _ = f
... | no  _ = μ x ⇒ N [ y := V ]

-- Examples
_ : (ƛ "z" ⇒ ` "s" · (` "s" · ` "z")) [ "s" := sucᶜ ]
      ≡ ƛ "z" ⇒ sucᶜ · (sucᶜ · ` "z")
_ = refl

_ : (sucᶜ · (sucᶜ · ` "z")) [ "z" := `zero ] ≡ sucᶜ · (sucᶜ · `zero)
_ = refl

_ : (ƛ "x" ⇒ ` "y") [ "y" := `zero ] ≡ ƛ "x" ⇒ `zero
_ = refl

_ : (ƛ "x" ⇒ ` "x") [ "x" := `zero ] ≡ ƛ "x" ⇒ ` "x"
_ = refl

_ : (ƛ "y" ⇒ ` "y") [ "x" := `zero ] ≡ ƛ "y" ⇒ ` "y"
_ = refl