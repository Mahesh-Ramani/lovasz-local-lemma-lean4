# Lovász Local Lemma in Lean 4 + Mathlib4

A formalization of the **Lovász Local Lemma** (LLL) in Lean 4, built on Mathlib4.
This appears to be the first complete machine-checked proof of the LLL in any proof assistant.

## Overview

The Lovász Local Lemma (Erdős–Lovász, 1975) is a cornerstone of the probabilistic method
in combinatorics. It guarantees that a collection of "bad" events can simultaneously be
avoided with positive probability, provided each event is unlikely and has limited
dependence on the others.

This repository formalizes the **asymmetric** and **symmetric** versions of the LLL,
along with the key auxiliary machinery used in the proof.

## Main Results

**`lovasz_local_lemma`** — Asymmetric LLL (measure lower bound).  
Let `(Ω, μ)` be a probability space, `{A i}` a finite family of measurable events,
and `Γ i` a dependency neighborhood for each `i` satisfying the lopsidependence condition.
If there exist `x i ∈ [0, 1)` such that for each `i`:

$$\mu(A_i) \leq x_i \prod_{j \in \Gamma(i)} (1 - x_j)$$

then:

$$\mu\!\Bigl(\bigcap_i (A_i)^c\Bigr) \;\geq\; \prod_i (1 - x_i)$$

**`lovasz_local_lemma_pos`** — The probability of avoiding all events is strictly positive under the asymmetric LLL conditions.

**`lovasz_local_lemma_symmetric`** — Symmetric LLL.  
If every event has probability at most `p`, every dependency neighborhood has size at most `d`,
and `4p(d+1) ≤ 1`, then `μ(⋂ i, (A i)ᶜ) > 0`.

## Proof Strategy

The proof follows Alon–Spencer, *The Probabilistic Method* (Chapter 5).

The core is a simultaneous strong induction (`lll_inductive`) establishing, for every
finite set `S`:
1. For all `i ∉ S`: `μ(A i ∩ avoidSet A S) ≤ x i · μ(avoidSet A S)`
2. `∏ j ∈ S, (1 - x j) ≤ μ(avoidSet A S)`

The inductive step splits `S` into neighbors `S₁ = S ∩ Γ(i)` and non-neighbors
`S₂ = S \ Γ(i)`. The lopsidependence condition decouples `A i` from `avoidSet A S₂`;
the **peeling lemma** (`lll_peeling`) then accumulates the product lower bound by
stripping events from `S₁` one at a time.

The symmetric version is reduced to the asymmetric one via the witness
`x i = 1 / (2(d+1))`, with Bernoulli's inequality used to verify the LLL condition.

## Dependencies

The formalization uses:
- **Lean 4** `v4.28.0`
- **Mathlib4** `v4.28.0`

Key Mathlib components: `MeasureTheory`, `ProbabilityTheory`,
`Finset.strongInduction`, `ENNReal` arithmetic.

## Repository Structure

```
RequestProject/
├── RequestProject/
│   └── LovaszLocalLemma.lean   -- All definitions and proofs
├── lakefile.toml
├── lake-manifest.json
├── lean-toolchain
└── README.md
```

## Key Definitions

| Name | Description |
|---|---|
| `LopsidependenceCondition` | `A i` is independent of `⋂ j ∈ S, (A j)ᶜ` for `S` outside `Γ i` |
| `avoidSet A S` | `⋂ j ∈ S, (A j)ᶜ` — event that none of the bad events in `S` occur |
| `LLL_Statement` | The combined inductive invariant used in the strong induction |

## Building

```bash
lake exe cache get   # fetch Mathlib cache
lake build
```

## References

- Erdős, P.; Lovász, L. (1975). "Problems and results on 3-chromatic hypergraphs and some related questions."
- Alon, N.; Spencer, J. (2016). *The Probabilistic Method*, 4th ed., Chapter 5. Wiley.
