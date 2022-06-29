module part1.Isomorphism where

{-
  Isomorphism as a way of asserting that two types are equal
  Embedding as a way of asserting that one type is smaller than another
-}
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; cong-app)
open Eq.≡-Reasoning
open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Nat.Properties using (+-comm)

-- Function composition
_∘_ : ∀ {A B C : Set} → (B → C) → (A → B) → A → C
(g ∘ f) x = g (f x)

{-
  Extensionality

  The only way to distinguish functions is by applying them.
  If two functions applied to the same argument always yield the
  same result, then they are the same function
-}
postulate
  extensionality : ∀ {A B : Set} {f g : A → B}
    → (∀ (x : A) → f x ≡ g x)
      -----------------------
    → f ≡ g

_+′_ : ℕ → ℕ → ℕ
m +′ zero  = m
m +′ suc n = suc (m +′ n)

same-app : ∀ (m n : ℕ) → m +′ n ≡ m + n
same-app m n 
  rewrite +-comm m n = helper m n
  where
    helper : ∀ (m n : ℕ) → m +′ n ≡ n + m
    helper m zero     = refl
    helper m (suc n)  = cong suc (helper m n)

same : _+′_ ≡ _+_
same = extensionality (λ m → extensionality (λ n → same-app m n))

postulate
  ∀-extensionality : ∀ {A : Set} {B : A → Set} {f g : ∀(x : A) → B x}
    → (∀ (x : A) → f x ≡ g x)
      -----------------------
    → f ≡ g

-- Isomorphism

infix 0 _≃_

record _≃_ (A B : Set) : Set where
  field
    to      : A → B
    from    : B → A
    from∘to : ∀ (x : A) → from (to x) ≡ x
    to∘from : ∀ (y : B) → to (from y) ≡ y

open _≃_

-- The above declaration is similar to the following
data _≃′_ (A B : Set): Set where
  mk-≃′ : ∀ (to : A → B) →
          ∀ (from : B → A) →
          ∀ (from∘to : (∀ (x : A) → from (to x) ≡ x)) →
          ∀ (to∘from : (∀ (y : B) → to (from y) ≡ y)) →
          A ≃′ B

to′ : ∀ {A B : Set} → (A ≃′ B) → (A → B)
to′ (mk-≃′ f g g∘f f∘g) = f

from′ : ∀ {A B : Set} → (A ≃′ B) → (B → A)
from′ (mk-≃′ f g g∘f f∘g) = g

from∘to′ : ∀ {A B : Set} → (A≃B : A ≃′ B) → (∀ (x : A) → from′ A≃B (to′ A≃B x) ≡ x)
from∘to′ (mk-≃′ f g g∘f f∘g) = g∘f

to∘from′ : ∀ {A B : Set} → (A≃B : A ≃′ B) → (∀ (y : B) → to′ A≃B (from′ A≃B y) ≡ y)
to∘from′ (mk-≃′ f g g∘f f∘g) = f∘g

-- Isomorphism is an equivalence (reflexive symmetric and transitive)
≃-refl : ∀ {A : Set}
    -----
  → A ≃ A
≃-refl = record
  { to = λ x → x
  ; from = λ y → y
  ; from∘to = λ y → refl
  ; to∘from = λ x → refl
  }

≃-sym : ∀ {A B : Set}
  → A ≃ B
    -----
  → B ≃ A
≃-sym A≃B = record
  { to = from A≃B
  ; from = to A≃B
  ; from∘to = to∘from A≃B
  ; to∘from = from∘to A≃B
  }

≃-trans : ∀ {A B C : Set}
  → A ≃ B
  → B ≃ C
    -----
  → A ≃ C
≃-trans A≃B B≃C = record
  { to = (to B≃C) ∘ (to A≃B)
  ; from = (from A≃B) ∘ (from B≃C)
  ; from∘to = λ{x →
      begin
        from A≃B (from B≃C (to B≃C (to A≃B x)))
      ≡⟨ cong (from A≃B) (from∘to B≃C (to A≃B x)) ⟩
        from A≃B (to A≃B x)
      ≡⟨ from∘to A≃B x ⟩
        x
      ∎
    }
  ; to∘from = λ{y → 
      begin
        to B≃C (to A≃B (from A≃B (from B≃C y)))
      ≡⟨ cong (to B≃C) (to∘from A≃B (from B≃C y)) ⟩
        to B≃C (from B≃C y)
      ≡⟨ to∘from B≃C y ⟩
        y
      ∎
    }
  }

module ≃-Reasoning where

  infix  1 ≃-begin_
  infixr 2 _≃⟨_⟩_
  infix  3 _≃-∎

  ≃-begin_ : ∀ {A B : Set}
    → A ≃ B
      -----
    → A ≃ B
  ≃-begin A≃B = A≃B

  _≃⟨_⟩_ : ∀ (A : Set) {B C : Set}
    → A ≃ B
    → B ≃ C
      -----
    → A ≃ C
  A ≃⟨ A≃B ⟩ B≃C = ≃-trans A≃B B≃C

  _≃-∎ : ∀ (A : Set)
      -----
    → A ≃ A
  A ≃-∎ = ≃-refl

open ≃-Reasoning

{-
  Embedding

  a weakening of Isomorphism. Shows that the first type is included in the second;
  there is a many-to-one correspondence between the second type and the first one.

  Is reflexive and transitive
-}
infix 0 _≲_

record _≲_ (A B : Set) : Set where
  field
    to      : A → B
    from    : B → A
    from∘to : ∀ (x : A) → from (to x) ≡ x

open _≲_

≲-refl : ∀ {A : Set} → A ≲ A
≲-refl =  record
  { to      = λ{x → x}
  ; from    = λ{y → y}
  ; from∘to = λ{x → refl}
  }

≲-trans : ∀ {A B C : Set} 
  → A ≲ B 
  → B ≲ C 
    -----
  → A ≲ C
≲-trans A≲B B≲C = record
  { to = (to B≲C) ∘ (to A≲B)
  ; from = (from A≲B) ∘ (from B≲C) 
  ; from∘to = λ{x → 
      begin
        from A≲B (from B≲C (to B≲C (to A≲B x)))
      ≡⟨ cong (from A≲B) (from∘to B≲C (to A≲B x)) ⟩
        from A≲B (to A≲B x)
      ≡⟨ from∘to A≲B x ⟩
        x
      ∎
    }
  }

{-
  If the two types embed in each other, and the embedding functions correspond, then
  they are isomorphic; this is a weak from of anti-symmetry
-}
≲-antisym : ∀ {A B : Set}
  → (A≲B : A ≲ B)
  → (B≲A : B ≲ A)
  → (to A≲B ≡ from B≲A)
  → (from A≲B ≡ to B≲A)
    -------------------
  → A ≃ B
≲-antisym A≲B B≲A to≡from from≡to = record
  { to = to A≲B
  ; from = from A≲B
  ; from∘to = from∘to A≲B
  ; to∘from = λ{y → 
      begin
        to A≲B (from A≲B y)
      ≡⟨ cong (to A≲B) (cong-app from≡to y) ⟩
        to A≲B (to B≲A y)
      ≡⟨ cong-app to≡from (to B≲A y) ⟩
        from B≲A (to B≲A y)
      ≡⟨ from∘to B≲A y ⟩
        y 
      ∎
    }
  }

module ≲-Reasoning where

  infix  1 ≲-begin_
  infixr 2 _≲⟨_⟩_
  infix  3 _≲-∎

  ≲-begin_ : ∀ {A B : Set}
    → A ≲ B
      -----
    → A ≲ B
  ≲-begin A≲B = A≲B

  _≲⟨_⟩_ : ∀ (A : Set) {B C : Set}
    → A ≲ B
    → B ≲ C
      -----
    → A ≲ C
  A ≲⟨ A≲B ⟩ B≲C = ≲-trans A≲B B≲C

  _≲-∎ : ∀ (A : Set)
      -----
    → A ≲ A
  A ≲-∎ = ≲-refl

open ≲-Reasoning

-- Exercise ≃-implies-≲
≃-implies-≲ : ∀ {A B : Set}
  → A ≃ B
    -----
  → A ≲ B
≃-implies-≲ A≃B = record
  { to = to A≃B
  ; from = from A≃B
  ; from∘to = from∘to A≃B
  }

{-
  Exercise _⇔_ 

  Equivalence of propositions (if and only if).
  Show that it is reflexive, symmetric and transitive
-}
infix 0 _⇔_

record _⇔_ (A B : Set) : Set where
  field
    to   : A → B
    from : B → A

open _⇔_

⇔-refl : ∀ {A : Set}
    -----
  → A ⇔ A
⇔-refl = record
  { to = λ x → x
  ; from = λ y → y
  }

⇔-sym : {A B : Set}
  → A ⇔ B
    -----
  → B ⇔ A
⇔-sym A⇔B = record
  { to = from A⇔B
  ; from = to A⇔B
  }

⇔-trans : {A B C : Set}
  → A ⇔ B
  → B ⇔ C
    -----
  → A ⇔ C
⇔-trans A⇔B B⇔C = record
  { to = (to B⇔C) ∘ (to A⇔B)
  ; from = (from A⇔B) ∘ (from B⇔C)
  }

{-
  Bin-embedding

  TODO

  Show that there is an embedding of ℕ into Bin
-}

{-
  Standard Library

  import Function using (_∘_)
  import Function.Inverse using (_↔_)
  import Function.LeftInverse using (_↞_)2
-}