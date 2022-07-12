module part1.Quantifiers where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_)
open import Relation.Nullary using (¬_)
open import Data.Product using (_×_; proj₁; proj₂) renaming (_,_ to ⟨_,_⟩)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import plfa.part1.Isomorphism using (_≃_; extensionality)
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