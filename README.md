# Erdős problems in Lean 4

Lean 4 / Mathlib proofs of two problems from [erdosproblems.com](https://www.erdosproblems.com).

| Problem | Result | File | Main theorems |
|---|---|---|---|
| [216](https://www.erdosproblems.com/216) | Horton (1983): for every `n` there are `n` points in the plane, no three collinear, with no empty convex 7-gon. So `g(k)` does not exist for `k ≥ 7`. | `Erdos/Erdos216.lean` | `Erdos216.erdos_216`, `Erdos216.erdos_216_of_seven_le` |
| [466](https://www.erdosproblems.com/466) | Graham: `N(X, 1/10) > (log X)/10`, hence `N(X, δ) → ∞` for `δ = 1/10`. | `Erdos/Erdos466.lean` | `Erdos466.erdos_466`, `Erdos466.erdos_466.variants.graham` |

Both files are self-contained (`import Mathlib` only), contain no `sorry`, and depend only on
the axioms `propext`, `Classical.choice`, `Quot.sound` (each file ends with `#print axioms`).

## Building

```
lake exe cache get
lake build
```

Toolchain: Lean `v4.33.1`, Mathlib `v4.33.1` (pinned in `lake-manifest.json`).

## Notes

* **216.** The formal statement was written for this repository. Its definitions of convex
  position and emptiness follow
  [EmptyHexagonLean](https://github.com/bsubercaseaux/EmptyHexagonLean) and
  [formal-conjectures](https://github.com/google-deepmind/formal-conjectures). The point set
  is `(i, Σ_j bit_j(i) / B^j)` for `i < n`, with `B = 2n + 3`. The file header outlines the
  proof.
* **466.** Definitions and statements are copied from
  `FormalConjectures/ErdosProblems/466.lean` in formal-conjectures. Another Lean proof of
  this problem exists in [plby/lean-proofs](https://github.com/plby/lean-proofs); the one
  here was written independently, using the points `(4^i, 2^i)`.

## Provenance

The proofs were written by Claude (Anthropic's AI model) in a session directed by the
repository owner, and checked by the Lean kernel as described above.
