# Induction

## Exercise: finite-|-assoc

- In the beginning, we know nothing.

- On the first day, we know zero

```
  0: ℕ
```

- On the second day, we know all cases of associativity with 0

```
  0: ℕ
  1: ℕ    (0 + 0) + 0 ≡ 0 + (0 + 0)
```

- On the third day, we know all cases of associativity with 0 and 1

```
  0: ℕ
  1: ℕ    (0 + 0) + 0 ≡ 0 + (0 + 0)
  2: ℕ    (1 + 0) + 0 ≡ 1 + (0 + 0)
          (0 + 1) + 0 ≡ 0 + (1 + 0)
          (0 + 0) + 1 ≡ 0 + (0 + 1)
          (1 + 1) + 0 ≡ 1 + (1 + 0)
          (1 + 0) + 1 ≡ 1 + (0 + 1)
          (0 + 1) + 1 ≡ 0 + (1 + 1)
          (1 + 1) + 1 ≡ 1 + (1 + 1)
```

- **TODO**: How many distinct equations do we know in the n-th day?