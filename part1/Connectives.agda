module part1.Connectives where

{-
  Logical connectives and their correspondance with data types
  (Proposition as Types):

  - conjunction is product
  - disjunction is sum
  - true is unit type
  - false is empty type
  - implication is function space
-}
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)
open Eq.≡-Reasoning
open import Data.Nat using (ℕ)
open import Function using (_∘_)
open import part1.Isomorphism using (_≃_; _≲_; extensionality)
open part1.Isomorphism.≃-Reasoning

data _×_ (A B : Set) : Set where

  ⟨_,_⟩ :
      A
    → B
      -----
    → A × B

infixr 2 _×_


{-
  Given the evidence that A × B holds, we can conclude
  that both A and B hold
-}
proj₁ : ∀ {A B : Set}
  → A × B
    -----
  → A
proj₁ ⟨ a , _ ⟩ = a 

proj₂ : ∀ {A B : Set}
  → A × B
    -----
  → B 
proj₂ ⟨ _ , b ⟩ = b

η-× : ∀ {A B : Set} (w : A × B) → ⟨ proj₁ w , proj₂ w ⟩ ≡ w
η-× ⟨ a , b ⟩ = refl

-- A variant of the same definition
record _×′_ (A B : Set) : Set where
  constructor ⟨_,_⟩′
  field
    proj₁′ : A
    proj₂′ : B
open _×′_

-- With record types, this holds by definition
η-×′ : ∀ {A B : Set} (w : A ×′ B) → ⟨ proj₁′ w , proj₂′ w ⟩′ ≡ w
η-×′ w = refl


data Bool : Set where
  true  : Bool
  false : Bool

data Tri : Set where
  aa : Tri
  bb : Tri
  cc : Tri

×-count : Bool × Tri → ℕ
×-count ⟨ true  , aa ⟩  =  1
×-count ⟨ true  , bb ⟩  =  2
×-count ⟨ true  , cc ⟩  =  3
×-count ⟨ false , aa ⟩  =  4
×-count ⟨ false , bb ⟩  =  5
×-count ⟨ false , cc ⟩  =  6

{-
  Product is commutative and associative up to isomorphism
-}
×-comm : ∀ {A B : Set} → A × B ≃ B × A
×-comm = record
  { to = λ{ ⟨ a , b ⟩ → ⟨ b , a ⟩ }
  ; from = λ{ ⟨ b , a ⟩ → ⟨ a , b ⟩ }
  ; from∘to = λ{ ⟨ a , b ⟩ → refl  }
  ; to∘from = λ{ ⟨ b , a ⟩ → refl }
  }

{-
  Being commutative is different from being commutative up to isomorphism:

  m * n ≡ n * m
  A × B ≃ B × A

  Bool × Tri is not the same as Tri × Bool, but there is an isomorphism between
  the two types, but there is an isomorphism between the two types. ⟨ true , aa ⟩
  corresponds to ⟨ aa , true ⟩

  Similarly, being associative is different from being associative up to isomorphism
-}
×-assoc : ∀ {A B C : Set} → (A × B) × C ≃ A × (B × C)
×-assoc = record
  { to = λ{ ⟨ ⟨ a , b ⟩ , c ⟩ → ⟨ a , ⟨ b , c ⟩ ⟩ }
  ; from = λ{ ⟨ a , ⟨ b , c ⟩ ⟩ → ⟨ ⟨ a , b ⟩ , c ⟩ } 
  ; from∘to = λ{ ⟨ ⟨ a , b ⟩ , c ⟩  → refl }
  ; to∘from = λ{ ⟨ a , ⟨ b , c ⟩ ⟩  → refl }
  }

{-
  Exercise ⇔≃×

  Show that A ⇔ B is isomorphic to (A → B) × (B → A)
-}
open import part1.Isomorphism using (_⇔_)
open _⇔_

⇔≃×-to : ∀ {A B : Set}
  → (A ⇔ B) → (A → B) × (B → A)
⇔≃×-to A⇔B = ⟨ to A⇔B , from A⇔B ⟩

⇔≃×-from : ∀ {A B : Set}
  → (A → B) × (B → A) → (A ⇔ B)
⇔≃×-from ⟨ A→B , B→A ⟩ = record
  { to = A→B
  ; from = B→A
  }

⇔≃× : ∀ {A B : Set}
  → (A ⇔ B) ≃ (A → B) × (B → A)
⇔≃× = record
  { to = ⇔≃×-to
  ; from = ⇔≃×-from
  ; from∘to = λ{ A⇔B →
      begin
        ⇔≃×-from (⇔≃×-to A⇔B)
      ≡⟨⟩
        record { to = to A⇔B ; from = from A⇔B }
      ∎
    }
  ; to∘from = λ{ ⟨ A→B , B→A ⟩ →  
      begin
        ⇔≃×-to (⇔≃×-from ⟨ A→B , B→A ⟩)
      ≡⟨⟩
        ⇔≃×-to (record { to = A→B ; from = B→A })
      ≡⟨⟩
        ⟨ A→B , B→A ⟩
      ∎
    }
  }

{-
  Truth is unit

  Truth T always holds. There is an introduction rule, but no 
  elimination rule 
-}

data ⊤ : Set where

  tt :
    --
    ⊤

η-⊤ : ∀ (w : ⊤) → tt ≡ w
η-⊤ tt = refl

-- We can declare truth as an empty record. record {} corresponds to tt′
record ⊤′ : Set where
  constructor tt′

η-⊤′ : ∀ (w : ⊤′) → tt′ ≡ w
η-⊤′ w = refl

-- Agda knows that any value of type ⊤′ must be tt′, so Agda can always infer it
truth′ : ⊤′
truth′ = _

-- ⊤ is the unit type, it has exactly one member
⊤-count : ⊤ → ℕ
⊤-count tt = 1

{-
  For numbers, 1 is the identity of multiplication. Similarly, unit is the identity
  of product up to isomorphism.

  Having an identity is different from having an identity up to isomorphism
-}

⊤-identityˡ : ∀ {A : Set} → ⊤ × A ≃ A
⊤-identityˡ = record 
  { to = λ{ ⟨ tt , a ⟩ → a  }
  ; from = λ{ a → ⟨ tt , a ⟩ }
  ; from∘to = λ{ ⟨ tt , a ⟩ → refl }
  ; to∘from = λ{ a → refl }
  }

-- Right identity follows from commutativity
⊤-identityʳ : ∀ {A : Set} → (A × ⊤) ≃ A
⊤-identityʳ {A} =
  ≃-begin
    (A × ⊤)
  ≃⟨ ×-comm ⟩
    (⊤ × A)
  ≃⟨ ⊤-identityˡ ⟩
    A
  ≃-∎

{-
  Disjunction is Sum

  Given two propositions A and B, A ⊎ B holds if either
  A holds or B holds

  Sum on types is also commutative and associative up to 
  isomorphism
-}

data _⊎_ (A B : Set) : Set where

  inj₁ :
      A
      -----
    → A ⊎ B

  inj₂ :
      B
      -----
    → A ⊎ B

infixr 1 _⊎_

{-
  inj₁ and inj₂ introduce a disjunction, and 
  case case-⊎ eliminates the disjunction

  when inj₁ and inj₂ appear at the right-hand side of an
  equation, they are constructors. If they appear at the left, 
  they are destructors
-}
case-⊎ : ∀ {A B C : Set}
  → (A → C)
  → (B → C)
  → A ⊎ B
    -----------
  → C
case-⊎ f g (inj₁ a) = f a
case-⊎ f g (inj₂ b) = g b

-- Applying the destructor to each of the constructors is the identity:
η-⊎ : ∀ {A B : Set} (w : A ⊎ B) → case-⊎ inj₁ inj₂ w ≡ w
η-⊎ (inj₁ x) = refl
η-⊎ (inj₂ y) = refl

uniq-⊎ : ∀ {A B C : Set} (h : A ⊎ B → C) (w : A ⊎ B) →
  case-⊎ (h ∘ inj₁) (h ∘ inj₂) w ≡ h w
uniq-⊎ h (inj₁ x) = refl
uniq-⊎ h (inj₂ y) = refl

⊎-count : Bool ⊎ Tri → ℕ
⊎-count (inj₁ true)   =  1
⊎-count (inj₁ false)  =  2
⊎-count (inj₂ aa)     =  3
⊎-count (inj₂ bb)     =  4
⊎-count (inj₂ cc)     =  5

{-
  Exercise ⊎-comm

  Show sum is commutative up to isomorphism.
-}
⊎-comm : ∀ {A B : Set}
  → A ⊎ B ≃ B ⊎ A
⊎-comm = record
  { to = λ 
    { (inj₁ a) → inj₂ a
    ; (inj₂ b) → inj₁ b
    }
  ; from = λ
    { (inj₁ b) → inj₂ b
    ; (inj₂ a) → inj₁ a
    }
  ; from∘to = λ
    { (inj₁ a) → refl
    ; (inj₂ b) → refl
    }
  ; to∘from = λ
    { (inj₁ b) → refl
    ; (inj₂ a) → refl
    }
  }

{-
  Exercise ⊎-assoc

  Show sum is associative up to isomorphism.
-}
⊎-assoc-to : ∀ {A B C : Set}
  → (A ⊎ B) ⊎ C → A ⊎ (B ⊎ C)
⊎-assoc-to (inj₁ (inj₁ a))  = inj₁ a
⊎-assoc-to (inj₁ (inj₂ b))  = inj₂ (inj₁ b)
⊎-assoc-to (inj₂ c)         = inj₂ (inj₂ c)

⊎-assoc-from : ∀ {A B C : Set}
  → A ⊎ (B ⊎ C) → (A ⊎ B) ⊎ C
⊎-assoc-from (inj₁ a)         = (inj₁ (inj₁ a))
⊎-assoc-from (inj₂ (inj₁ b))  = (inj₁ (inj₂ b))
⊎-assoc-from (inj₂ (inj₂ c))  = (inj₂ c)

⊎-assoc-from∘to : ∀ {A B C : Set}
  → (x : (A ⊎ B) ⊎ C) 
  → ⊎-assoc-from (⊎-assoc-to x) ≡ x
⊎-assoc-from∘to (inj₁ (inj₁ a)) = refl
⊎-assoc-from∘to (inj₁ (inj₂ b)) = refl
⊎-assoc-from∘to (inj₂ c)        = refl

⊎-assoc-to∘from : ∀ {A B C : Set}
  → (y : A ⊎ B ⊎ C) 
  → ⊎-assoc-to (⊎-assoc-from y) ≡ y
⊎-assoc-to∘from (inj₁ a)        = refl
⊎-assoc-to∘from (inj₂ (inj₁ b)) = refl
⊎-assoc-to∘from (inj₂ (inj₂ c)) = refl

⊎-assoc : ∀ {A B C : Set}
  → (A ⊎ B) ⊎ C ≃ A ⊎ (B ⊎ C)
⊎-assoc = record
  { to = ⊎-assoc-to
  ; from = ⊎-assoc-from
  ; from∘to = ⊎-assoc-from∘to
  ; to∘from = ⊎-assoc-to∘from
  }

{-
  False is empty

  False never holds
-}
data ⊥ : Set where
  -- no clauses!
  
