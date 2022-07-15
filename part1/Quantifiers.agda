module part1.Quantifiers where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; sym; cong)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_)
open import Relation.Nullary using (¬_)
open import Data.Product using (_×_; proj₁; proj₂) renaming (_,_ to ⟨_,_⟩)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import plfa.part1.Isomorphism using (_≃_; extensionality; _⇔_)
open import Function using (_∘_)

{-
  Universals

  Given a variable x of type A, and a proposition B x which contains x as a free variable,
  the universally quantified proposition ∀ (x : A) → B x (here x is a bounded variable) holds 
  if for every term M of type A the proposition B M holds.

  Evidence that ∀ (x : A) → B x holds is of the form

    λ (x : A) → N x

  Where N x : B x
-}
∀-elim : ∀ { A : Set } { B : A → Set }
  → (f : ∀ (x : A) → B x)
  → (a : A)
    ---------------------
  → B a
∀-elim f a = f a

{-
  Exercise ∀-distrib-×

  Universals distribute over conjunctions.

  This isomorphism is very similar to the one presented in `→-distrib-×`
  with the exception that, in this case, we don't need extensionality to prove
  from∘to.

  In →-distrib-× we had to prove that:

    (λ a → ⟨ proj₁ (f a) , proj₂ (f a) ⟩) ≡ f

  Here we have to prove that:

    (λ { ⟨ g , h ⟩ → λ a → ⟨ g a , h a ⟩ })
      ⟨ (λ x → proj₁ (f x)) , (λ x → proj₂ (f x)) ⟩
      ≡ f

  λ { ⟨ g , h ⟩ → λ a → ⟨ g a , h a ⟩ } is given by η-× ∘ f in the
  →-distrib-× case
-}
∀-distrib-× : ∀ {A : Set} {B C : A → Set} →
  (∀ (x : A) → B x × C x) ≃ (∀ (x : A) → B x) × (∀ (x : A) → C x)
∀-distrib-× = record 
  { to = λ f → ⟨ proj₁ ∘ f , proj₂ ∘ f ⟩
  ; from = λ{ ⟨ g , h ⟩ → λ a → ⟨ g a , h a ⟩  }
  ; from∘to = λ f → refl
  ; to∘from = λ{ ⟨ f , g ⟩ → refl }
  }

{-
  ⊎∀-implies-∀⊎

  Disjunction of universals implies a universal of disjunctions.

  The converse does not hold, since we need to build a function of type

    (∀ (x : A) → B x) ⊎ (∀ (x : A) → C x)

    inj₁ (λ x → ?) or inj₂ (λ x → ?)

  But if we apply x to ∀ (x : A) → B x ⊎ C x, we can not know concretely
  if we have B x or C x
-}
⊎∀-implies-∀⊎ : ∀ {A : Set} {B C : A → Set} →
  (∀ (x : A) → B x) ⊎ (∀ (x : A) → C x) → ∀ (x : A) → B x ⊎ C x
⊎∀-implies-∀⊎ (inj₁ f) = inj₁ ∘ f
⊎∀-implies-∀⊎ (inj₂ g) = inj₂ ∘ g

{-
  Exercise ∀-×

  Let B be a type indexed by Tri, that is B : Tri → Set. Show that ∀ (x : Tri) → B x is isomorphic to B aa × B bb × B cc
-}
data Tri : Set where
  aa : Tri
  bb : Tri
  cc : Tri

postulate
  ∀-extensionality : ∀ {A : Set} {B : A → Set} {f g : ∀(x : A) → B x}
    → (∀ (x : A) → f x ≡ g x)
      -----------------------
    → f ≡ g

∀-distrib-Tri-× : ∀ { B : Tri → Set }
  → (∀ (x : Tri) → B x) ≃ B aa × B bb × B cc
∀-distrib-Tri-× = record
  { to = λ f → ⟨ f aa , ⟨ f bb , f cc ⟩ ⟩
  ; from = λ{ ⟨ Baa , ⟨ Bbb , Bcc ⟩ ⟩ → λ
    { aa → Baa
    ; bb → Bbb
    ; cc → Bcc
    } 
  }
  ; from∘to = λ f → ∀-extensionality λ
    { aa → refl
    ; bb → refl
    ; cc → refl
    }
  ; to∘from = λ{ ⟨ Baa , ⟨ Bbb , Bcc ⟩ ⟩ → refl }
  }

{-
  Existentials

  Products arise as a special case of existentials, where the second component does not depend on a variable drawn from the first component.
-}
data Σ (A : Set) (B : A → Set) : Set where
  ⟨_,_⟩ : (x : A) → B x → Σ A B

record Σ′ (A : Set) (B : A → Set) : Set where
  field
    proj₁′ : A
    proj₂′ : B proj₁′

{-
  this special syntax declaration specifies that the term on the left may be written with the syntax on the right. 
  The special syntax is available only when the identifier Σ-syntax is imported.
-}
Σ-syntax = Σ
infix 2 Σ-syntax
syntax Σ-syntax A (λ x → B) = Σ[ x ∈ A ] B

∃ : ∀ {A : Set} (B : A → Set) → Set
∃ {A} B = Σ A B

∃-syntax = ∃
syntax ∃-syntax (λ x → B) = ∃[ x ] B

∃-elim : ∀ {A : Set} {B : A → Set} {C : Set}
  → (∀ x → B x → C)
  → ∃[ x ] B x
    ---------------
  → C
∃-elim f ⟨ x , y ⟩ = f x y

-- Generaliza
∀∃-currying : ∀ {A : Set} {B : A → Set} {C : Set}
  → (∀ x → B x → C) ≃ (∃[ x ] B x → C)
∀∃-currying = record
  { to = λ f → λ{ ⟨ x , Bx ⟩ → f x Bx }
  ; from = λ g → λ x → λ Bx → g ⟨ x , Bx ⟩
  ; from∘to = λ f → refl
  ; to∘from = λ g → extensionality λ{ ⟨ x , Bx ⟩ → refl }
  }

{-
  Exercise ∃-distrib-⊎

  existentials distribute over disjunction
-}
∃-distrib-⊎ : ∀ {A : Set} {B C : A → Set} →
  ∃[ x ] (B x ⊎ C x) ≃ (∃[ x ] B x) ⊎ (∃[ x ] C x)
∃-distrib-⊎ = record
  { to = λ
    { ⟨ x , inj₁ Bx ⟩ → inj₁ ⟨ x , Bx ⟩
    ; ⟨ x , inj₂ Cx ⟩ → inj₂ ⟨ x , Cx ⟩
    }
  ; from = λ
    { (inj₁ ⟨ x , Bx ⟩) → ⟨ x , inj₁ Bx ⟩
    ; (inj₂ ⟨ x , Cx ⟩) → ⟨ x , inj₂ Cx ⟩
    }
  ; from∘to = λ
    { ⟨ x , inj₁ Bx ⟩ → refl
    ; ⟨ x , inj₂ Cx ⟩ → refl
    }
  ; to∘from = λ
    { (inj₁ ⟨ x , Bx ⟩) → refl
    ; (inj₂ ⟨ x , Cx ⟩) → refl
    }
  }
{-
  Exercise ∃×-implies-×∃

  existential of conjunctions implies a conjunction of existentials

  The converse does not hold, since for

    (∃[ x1 ] B x1) × (∃[ x2 ] C x2)

  x1 may be different from x2, and so, we can not unify them into

    ∃[ x ] (B x × C x)

  (the x that makes ∃[ x ] B x hold, may be different from the one that
  makes ∃[ x2 ] C x2 hold)
-}
∃×-implies-×∃ : ∀ {A : Set} {B C : A → Set} →
  ∃[ x ] (B x × C x) → (∃[ x ] B x) × (∃[ x ] C x)
∃×-implies-×∃ ⟨ x , ⟨ Bx , Cx ⟩ ⟩ = ⟨ ⟨ x , Bx ⟩ , ⟨ x , Cx ⟩ ⟩ 

{-
  An existential example

  even n iff ∃[ m ] ( m * 2 ≡ n)

  odd n iff ∃[ m ] (1 + m * 2 ≡ n)
-}
open import part1.Relations using (even; odd)

even-∃ : ∀ {n : ℕ} → even n → ∃[ m ] (    m * 2 ≡ n)
odd-∃  : ∀ {n : ℕ} →  odd n → ∃[ m ] (1 + m * 2 ≡ n)

even-∃ even.zero        = ⟨ zero , refl ⟩
even-∃ (even.suc odd_n) 
    {-
      Inductive case. Prove that

        even (suc n) → ∃[ m ] (m * 2 ≡ suc n)

      We have that (odd n) holds since even (suc n) holds. Hence:

        odd-∃ odd_n → ∃[ m ] (1 + m * 2 ≡ n)
                    → ⟨ m , refl ⟩

      We need to prove that ∃[ m' ] (m' * 2 ≡ suc (suc (m * 2)))
      
      If m' = suc m, then 

        (suc m) * 2 ≡ 2 + m * 2 ≡ suc (suc (m * 2))
    -}
    with odd-∃ odd_n 
... | ⟨ m , refl ⟩ = ⟨ suc m , refl ⟩

odd-∃ (odd.suc even_n) 
    {-
      Inductive case. Prove that

        odd (suc n) → ∃[ m ] (1 + m * 2 ≡ suc n)

      We have that (even n) holds since odd (suc n) holds. Hence:

        even-∃ even_n → ∃[ m ] (m * 2 ≡ n)
                      → ⟨ m , refl ⟩

      We need to prove that ∃[ m' ] (1 + m' * 2 ≡ suc (m * 2)),
      which holds if m' = m
    -}
    with even-∃ even_n
... | ⟨ m , refl ⟩ = ⟨ m , refl ⟩

∃-even : ∀ {n : ℕ} → ∃[ m ] (    m * 2 ≡ n) → even n
∃-odd  : ∀ {n : ℕ} → ∃[ m ] (1 + m * 2 ≡ n) →  odd n

∃-even ⟨ zero , refl ⟩  = even.zero
∃-even ⟨ suc m , refl ⟩ = even.suc (∃-odd ⟨ m , refl ⟩)

∃-odd ⟨ m , refl ⟩ = odd.suc (∃-even ⟨ m , refl ⟩)

{-
  Exercise ∃-even-odd

  2 * m ≡ suc (suc zero) * m
        ≡ m + (suc zero) * m
        ≡ m + (m + zero * m)
        ≡ m + (m + zero)
-}
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; step-≡; _∎)
open import Data.Nat.Properties using (+-assoc; +-identityʳ; +-suc; +-comm)

even-∃' : ∀ {n : ℕ} → even n → ∃[ m ] (    2 * m ≡ n)
odd-∃'  : ∀ {n : ℕ} →  odd n → ∃[ m ] (2 * m + 1 ≡ n)

even-∃' even.zero    = ⟨ zero , refl ⟩
even-∃' (even.suc odd_n)
    with odd-∃' odd_n
... | ⟨ m , refl ⟩ = ⟨ suc m , 2*m≡n m ⟩
  where
    2*m≡n : ∀ (m : ℕ) → suc m + (suc m + 0) ≡ suc (m + (m + 0) + 1)
    2*m≡n m
      rewrite +-comm (m + (m + 0)) 1 
      | +-identityʳ m 
      | +-suc m m = refl

odd-∃' (odd.suc even_n) 
    with even-∃' even_n
... | ⟨ m , refl ⟩ = ⟨ m , +-comm (m + (m + 0)) 1 ⟩ 


{- 
  For some reason, Agda says this recursion does not terminate.
  If we define the functions with curried parameters instead of
  a pair, it works

  ∃-even' : ∀ {n : ℕ} → ∃[ m ] (    2 * m ≡ n) → even n
  ∃-odd'  : ∀ {n : ℕ} → ∃[ m ] (2 * m + 1 ≡ n) →  odd n

  ∃-even' ⟨ zero , refl ⟩  = even.zero
  ∃-even' ⟨ suc m , refl ⟩ = even.suc (∃-odd' ⟨ m , 2*m+1≡n m ⟩) 
    where
      2*m+1≡n : ∀ (m : ℕ) → 2 * m + 1 ≡ m + 1 * suc m
      2*m+1≡n m 
        rewrite +-suc m (m + 0) 
        | +-suc (m + (m + 0)) 0
        | sym (+-assoc m m 0)
        | +-identityʳ (m + m) 
        | +-identityʳ (m + m) = refl

  ∃-odd' ⟨ m , refl ⟩ 
    rewrite +-comm (m + (m + 0)) 1 = odd.suc (∃-even' ⟨ m , refl ⟩)
-}
∃-even' : ∀ {n : ℕ} (m : ℕ) → (    2 * m ≡ n) → even n
∃-odd'  : ∀ {n : ℕ} (m : ℕ) → (2 * m + 1 ≡ n) →  odd n

∃-even' zero refl    = even.zero
∃-even' (suc m) refl = even.suc (∃-odd' m (2*m+1≡n m)) 
  where
    2*m+1≡n : ∀ (m : ℕ) → 2 * m + 1 ≡ m + 1 * suc m
    2*m+1≡n m 
      rewrite +-suc m (m + 0) 
      | +-suc (m + (m + 0)) 0
      | sym (+-assoc m m 0)
      | +-identityʳ (m + m) 
      | +-identityʳ (m + m) = refl

∃-odd' m refl 
  rewrite +-comm (m + (m + 0)) 1 = odd.suc (∃-even' m refl)

{-
  Exercise ∃-+-≤

  Show that y ≤ z holds if and only if there exists a x such that x + y ≡ z
-}
open import part1.Relations using (_≤_; ≤-refl)
open _≤_
open _⇔_

∃-+-≤-to : ∀ {y z : ℕ} 
  → y ≤ z → (∃[ x ] (x + y ≡ z))
∃-+-≤-to {.0} {zero} z≤n = ⟨ zero , refl ⟩
∃-+-≤-to {.0} {suc z} z≤n = ⟨ suc z , +-identityʳ (suc z) ⟩
{-
  Inductive Case. Prove that:
    s≤s y<z → (∃[ x ] (x + suc y ≡ suc z))

  By Inductive Hypothesis, we know that ∃[ k ] (k + y ≡ z)

  If x = k
  x + suc y ≡ k + suc y
            ≡ suc (k + y)
            ≡ suc z
-}
∃-+-≤-to {suc y} {suc z} (s≤s y<z) 
    with ∃-+-≤-to y<z 
... | ⟨ k , refl ⟩ = ⟨ k , +-suc k y ⟩

∃-+-≤-from : ∀ {y z : ℕ} 
  → (∃[ x ] (x + y ≡ z)) → y ≤ z
∃-+-≤-from {y} {z} ⟨ zero , refl ⟩          = ≤-refl
∃-+-≤-from {zero} {suc z} ⟨ suc x , refl ⟩  = z≤n
∃-+-≤-from {suc y} {suc z} ⟨ suc x , e ⟩    = s≤s (∃-+-≤-from ⟨ suc x , sucx+y≡z e ⟩)
  where 
    sucx+y≡z : ∀ {x y z : ℕ}
      → suc (x + suc y) ≡ suc z
      → suc x + y ≡ z
    sucx+y≡z {x} {y} {z} refl
      rewrite +-suc x y = refl

∃-+-≤ : ∀ {y z : ℕ} 
  → (y ≤ z) ⇔ (∃[ x ] (x + y ≡ z))
∃-+-≤ = record 
  { to = ∃-+-≤-to 
  ; from = ∃-+-≤-from 
  }

{-
  Existentials, Universals, and Negation
-}
¬∃≃∀¬ : ∀ {A : Set} {B : A → Set}
  → (¬ ∃[ x ] B x) ≃ ∀ x → ¬ B x
¬∃≃∀¬ = record 
  { to = λ ¬∃x:Bx x Bx → ¬∃x:Bx ⟨ x , Bx ⟩ 
  ; from = λ{ ∀x:¬Bx ⟨ x , Bx ⟩ → (∀x:¬Bx x) Bx} 
  ; from∘to = λ ¬∃x:Bx → extensionality λ{ ⟨ x , Bx ⟩ → refl } 
  ; to∘from = λ ∀x:¬Bx → refl 
  }

{-
  Exercise ∃¬-implies-¬∀
  Show that existential of a negation implies negation of a universal

  We cannot prove the converse scenario, just from the fact that ¬ (∀ x → B x),
  we can not derive a particular x for wich B x does not hold
-}
∃¬-implies-¬∀ : ∀ {A : Set} {B : A → Set}
  → ∃[ x ] (¬ B x)
    --------------
  → ¬ (∀ x → B x)
∃¬-implies-¬∀ ⟨ x , ¬Bx ⟩ ∀x:Bx = ¬Bx (∀x:Bx x)