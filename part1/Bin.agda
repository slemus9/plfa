module part1.Bin where

open import Data.Nat using (ℕ; zero; suc; _+_; _*_)

data Bin : Set where
  ⟨⟩ : Bin
  _O : Bin → Bin
  _I : Bin → Bin

inc : Bin → Bin
inc ⟨⟩    = ⟨⟩ I
inc (b O) = b I
inc (b I) = (inc b) O

to : ℕ → Bin
to zero     = ⟨⟩ O
to (suc n)  = inc (to n)

from : Bin → ℕ
from ⟨⟩     = zero
from (b O)  = 2 * from b 
from (b I)  = 1 + 2 * from b