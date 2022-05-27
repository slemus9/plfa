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

Let a bitstring be $b_n\,...\,b_1\,b_0\;\;,b_i \in \{0,1\}$, that represents the natural number $b_02^0 + b_12^1 + ... + b_n2^n$

To increase a bitstring by 1, we evaluate the following 3 cases

- `inc ⟨⟩`: if the bitstring is empty, the number should be 1

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
$$y \in \N$$
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

