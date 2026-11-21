# Erdős problems in Lean 4

Lean 4 / Mathlib proofs of two problems from [erdosproblems.com](https://www.erdosproblems.com).

| Problem | Result | Where |
|---|---|---|
| [216](https://www.erdosproblems.com/216) | Horton (1983): for every `n` there are `n` points in the plane, no three collinear, with no empty convex 7-gon. So `g(k)` does not exist for `k ≥ 7`. | Statement: `Challenge.lean`. Proof: `Erdos/Erdos216.lean`, re-exported in `Solution.lean`. |
| [466](https://www.erdosproblems.com/466) | Graham: `N(X, 1/10) > (log X)/10`, hence `N(X, δ) → ∞` for `δ = 1/10`. | `Erdos/Erdos466.lean` (`Erdos466.erdos_466`, `Erdos466.erdos_466.variants.graham`) |

No file contains `sorry` except `Challenge.lean`, which is the statement-only file and has one
deliberate `sorry` per theorem. The proved theorems depend only on the axioms `propext`,
`Classical.choice` and `Quot.sound`.

## Problem 216: what is proved

`Challenge.lean` is the short file to read. It imports only Mathlib and states:

* `Erdos216.erdos_216`: for every `n` there are `n` points, no three on a line, with no
  empty convex 7-gon.
* `Erdos216.erdos_216_of_seven_le`: the same for every `k ≥ 7`.
* `Erdos216.cardSet_eq_empty`: for `k ≥ 7` no `N` has the property that every `N` points in
  general position contain an empty convex `k`-gon.
* `Erdos216.not_forall_cardSet_nonempty`: it is not the case that `g(k)` exists for every `k`.

`Solution.lean` proves the same four declarations from `Erdos/Erdos216.lean`. The point set
is `(i, Σ_j bit_j(i) / B^j)` for `i < n`, with `B = 2n + 3`; the header of
`Erdos/Erdos216.lean` outlines the proof.

"Empty" means that no other point of the set lies in the closed convex hull of the `k`
points. For sets with no three collinear points this is the same as having no other point in
the interior.

## Building and checking

```
lake exe cache get
lake build
python3 scripts/check-lean-sources.py
ruby scripts/validate-formalization.rb
./scripts/verify-comparator.sh      # needs bubblewrap
```

Toolchain: Lean `v4.36.0`, Mathlib `v4.36.0` (pinned in `lake-manifest.json`).

The layout (`Challenge.lean`, `Solution.lean`, `comparator.json`, `formalization.yaml`)
follows the [Palomar registry](https://palomar-registry.org/) template. `formalization.yaml`
records sources, scope, automation and review status.

## Notes

* **216.** The formal statement was written for this repository. Its definitions of convex
  position and emptiness follow
  [EmptyHexagonLean](https://github.com/bsubercaseaux/EmptyHexagonLean) and
  [formal-conjectures](https://github.com/google-deepmind/formal-conjectures).
* **466.** Definitions and statements are copied from
  `FormalConjectures/ErdosProblems/466.lean` in formal-conjectures. Another Lean proof of
  this problem exists in [plby/lean-proofs](https://github.com/plby/lean-proofs); the one
  here was written independently, using the points `(4^i, 2^i)`.
* An earlier commit (`a5e18e5`) has the same proofs for Lean and Mathlib `v4.33.1`, without
  the module system.

## Provenance

The statements and proofs were written by Claude (Anthropic's AI model) in a session directed
by the repository owner, and checked by the Lean kernel as described above. See
`formalization.yaml` for details, including the review status of the statement.

## License

Apache License 2.0, see `LICENSE`.
