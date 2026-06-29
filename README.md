# Wilson's Theorem in Lean 4

A formalization of Wilson's theorem and a prime-generating function in Lean 4, using [Mathlib](https://github.com/leanprover-community/mathlib4). The underlying proof is primary based on [this](https://www.youtube.com/watch?v=8JaZ7Gr-Z5A) video by Michael Penn at Randolph College.

## Goals

1. **Wilson's Theorem** — prove the biconditional:
   $$n \text{ is prime} \iff (n - 1)! \equiv -1 \pmod{n}$$

2. **Prime Generator** — define and verify the function `primeGenerator`, which uses Wilson's theorem to detect primes:
   $$\text{primeGenerator}(n) = \left\lfloor \frac{(n - 1)! \bmod n}{n-1} \right\rfloor \cdot (n - 2) + 2$$
   This outputs the next prime after $n$ when $n$ is prime, and $2$ otherwise.

## Proof Sketch (Wilson's Theorem)

**($\Rightarrow$)** Suppose $n = p$ is prime. Consider the set $S = \{2, 3, \ldots, p-2\}$. Since $\mathbb{Z}/p\mathbb{Z}$ is a field, every element of $S$ has a multiplicative inverse, and that inverse also lies in $S$ (since $a^2 \equiv 1 \pmod{p}$ would force $a \equiv \pm 1$, which are excluded from $S$). So the elements of $S$ pair up as $(a, a^{-1})$, and the product over $S$ is $1$. Therefore:

$$(p-1)! = 1 \cdot \underbrace{2 \cdots (p-2)}_{\prod S \,=\, 1} \cdot (p-1) \equiv -1 \pmod{p}$$

**($\Leftarrow$)** If $n$ is composite, one shows $(n-1)! \equiv 0 \pmod{n}$, not $-1$.

The Lean proof formalizes the forward direction via two lemmas:
- **Lemma A** — the only self-inverses mod $p$ are $\pm 1$
- **Lemma B** — $p - 1 \equiv -1 \pmod{p}$

## Building

Requires [Lean 4](https://leanprover.github.io/) (`v4.29.1`) and [Lake](https://github.com/leanprover/lake).

```bash
git clone https://github.com/adimchimma/lean-wilsons-theorem-primes.git
cd lean-wilsons-theorem-primes
lake build
```

The first build will download Mathlib and its compiled cache, which may take a few minutes.

