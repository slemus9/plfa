# Relations 

Let `n R m` be a binary relation between `n` and `m`. These
are some of the properties a relation may have:

- **Reflexive**: for all `n`, the relation `n R n` holds.
- **Transitive**: for all `m`, `n`, and `p`, if `m R n` and `n R p` hold, then `m R p` holds.
- **Anti-Symmetric**: for all `m`, `n`, if both `m R n` and `n R m` hold, then `m ≡ n` holds.
- **Total**: for all `m`, `n`, either `m R n` or `n R m` hold.

These are some combinations of the previous properties:

- **Preorder**: any relation that is **reflexive** and **transitive**
- **Partial order**: any **preorder** that is also **anti-symmetric**
- **Total order**: any **partial order** that is also **total** 

# Properties of ordering relations

The relation `≤` is a **Total Order** relation.

# Exercises

## Exercise: ordering

**TODO**

## Exercise: ≤-antisym-cases

```agda
≤-antisym : ∀ {m n : ℕ}
  → m ≤ n
  → n ≤ m
    -----
  → m ≡ n
≤-antisym z≤n       z≤n        =  refl
≤-antisym (s≤s m≤n) (s≤s n≤m)  =  cong suc (≤-antisym m≤n n≤m)
```
Omitted cases: 

- `≤-antisym z≤n (s≤s n≤m)`: the parameters imply that we have evidence for `0 ≤ n` and `suc n ≤ suc 0`, but this can only be true if `n = 0`
- `≤-antisym (s≤s m≤n) z≤n`: the parameters imply that we have evidence for `suc m ≤ 0` and `0 ≤ m`, but this can only be true if `m = 0`
