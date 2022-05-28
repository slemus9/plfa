# Naturals

# Bitstring

```agda
data Bin : Set where
  ⟨⟩ : Bin
  _O : Bin → Bin
  _I : Bin → Bin
```

## inc

```agda
inc : Bin → Bin
```

Let a bitstring $b_n\,...\,b_1\,b_0$, $b_i \in \{0,1\}$ represent the natural number $b_02^0 + b_12^1 + ... + b_n2^n$

To increase a bitstring by 1, we evaluate the following 3 cases

- `inc ⟨⟩`: if the bitstring is empty, the next number should be 1

```agda
inc ⟨⟩ = ⟨⟩ I
```

- `inc (b O)`: If the bitstring starts with 0 (even), we can just replace it with a 1, so that we add $2^0 = 1$ to the represented number:

```agda
inc (b O) = b I
```
- `inc (b I)`: If a bitstring of size $m$ starts with a chain of $1$'s of size $n$:

$$b_m\,b_{m-1}\,...\,0\,1_{n-1}\,...\,1_1\,1_0$$

the represented natural number $x$ can be expressed as:

$$x = y + S_{n-1}$$

$$y \in \mathbb{N}$$

$$S_n = \sum_{i=0}^n 2^i$$

and $S_n$ can be expressed as:

$$
\begin{align*}
2S_n - S_n &= 2^{n+1} - 1 \\
S_n &= 2^{n+1} - 1
\end{align*}
$$

hence, if we increase the number by one, we obtain the following:

$$
\begin{align*}
x + 1 &= y + S_{n-1} + 1 \\
x + 1 &= y + 2^{n}
\end{align*}
$$

This means that, to increase the bitstring by one, we can change the $n$-th bit to 1, and leave $b_{n-1}=...=b_1=b_0=0$:

$$b_m\,b_{m-1}\,...\,1\,0_{n-1}\,...\,0_1\,0_0$$

As a result we obtain the following definition:

```agda
inc : Bin → Bin
inc ⟨⟩ = ⟨⟩ I
inc (b O) = b I
inc (b I) = (inc b) O
```

## to

```agda
to : ℕ → Bin
```
Since `suc n = n + 1`, the bitstring representation of `suc n` can be expressed as `to (suc n) = inc (to n)`

```agda
to : ℕ → Bin
to zero   = ⟨⟩ O
to (suc n)  = inc (to n)
```
## from 

Let a bitstring $b_n\,...\,b_1\,b_0$, $b_i \in \{0,1\}$ represent the natural number $b_02^0 + b_12^1 + ... + b_n2^n = x$, which can also be expressed as:

$$
\begin{align*}
x &= b_0 + b_12^1 + ... + b_n2^n \\
  &= b_0 + 2(b_1 + b_22 + ... + b_n2^{n-1}) \\
  &= b_0 + 2(b_1 + 2(b_2 + b_32 + ... + b_n2^{n-2})) \\
  &=...
\end{align*}
$$

from this, we can define the following recursion to transform a bitstring to a natural number:

$$
\begin{align*}
from(0)           &= 0 \\
from(b_{i+1}\,b_i)&= b_i + 2 \cdot from(b_{i+1})
\end{align*}
$$

```agda
from : Bin → ℕ
from ⟨⟩     = zero
from (b O)  = 2 * from b 
from (b I)  = 1 + 2 * from b
```