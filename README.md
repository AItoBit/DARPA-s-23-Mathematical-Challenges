# DARPA mathematical challenges: formal developments

This repository currently contains a Lean 4 proof of the classical obstruction
to lifting a **discrete matrix representation across a square-zero ring
extension**. DARPA Mathematical Challenge 18 motivated the development.
The repository does not claim to solve the broader homotopy/Langlands research
agenda or the other DARPA challenges.

## Precise result

Let `f : R →+* S` be a surjective homomorphism of commutative rings. Assume
`a * b = 0` whenever `f a = 0` and `f b = 0`. Let `G` be a group, `n` a finite
index type with decidable equality, and `ρ : G →* (Matrix n n S)ˣ` a
representation. Reduction of invertible matrices along `f` is surjective and
has an abelian kernel `K`.

Conjugation by chosen lifts of `ρ` defines a `G` action on the additive group
underlying `K`. The defect `l(g) l(h) l(gh)⁻¹` is a 2-cocycle for that action.
Its class `obstruction f hf hsq ρ` in `H²(G, Additive K)` satisfies:

```lean
Darpa018.RepresentationLifting.obstruction_zero_iff_lift
  : obstruction f hf hsq ρ = 0 ↔
      ∃ ρ' : G →* (Matrix n n R)ˣ, (reduction f).comp ρ' = ρ
```

The coefficient group is regarded as a module over the integers; it is not
the trivial coefficient group `ℤ`. The action is induced by `ρ` and need not
be trivial. Empty matrix index types and trivial groups are allowed. No
nontriviality hypothesis is needed; the proof also covers these degenerate
cases. The main statement uses types in `Type`, while the matrix lemmas are
universe-polymorphic.

## Proof and scope

`Solution.lean` contains the entire substantive development, including all six
initial H² and matrix lemmas and 14 additional theorems. It proves that the
section equation is equivalent to being a coboundary, lifts invertible
matrices using square-zero inverse corrections, constructs the extension
cocycle, and corrects pointwise lifts to homomorphisms when its class vanishes.
It also identifies the underlying additive kernel with matrices whose entries
lie in `RingHom.ker f` via `u ↦ u - 1` and `X ↦ 1 + X`.

The development proves independence of **vanishing** from the chosen lifts.
It does not prove literal equality of classes under different action
presentations, or transport the H² class along an equivariant coefficient
identification. There are no topology, continuity, profinite, derived,
automorphic, or Langlands correspondence claims.

This is a formalization of classical obstruction theory. No new mathematical
result or priority of formalization is claimed. The user supplied the initial
six Lean lemmas and requested their completion and publication. Codex agents
developed the remaining proof, checked it with Lean, and performed a distinct
source and statement audit. No independent human expert review is claimed.

## Reproduce the checks

The package pins Lean `v4.35.0-rc3` and Mathlib commit
`0db6cb99b412983de54b59ecc1b0b2747542cda3`. With elan and Lake installed:

```sh
lake exe cache get
lake --wfail build Solution
lake build Challenge
lake env lean -DwarningAsError=true Audit.lean
```

`Solution.lean` has no proof holes or new axioms. `Audit.lean` prints the
transitive axioms of all 20 theorems and the elaborated main statement.
The permitted logical axioms are `propext`, `Classical.choice`, and
`Quot.sound`. There is no `native_decide` or `Lean.ofReduceBool` dependency.

`Challenge.lean` is a standalone statement specification using only Mathlib
imports. Its five deliberate proposition holes are expected: the full proof
is in `Solution.lean`. All computational definitions needed to specify the
obstruction are explicit. `comparator.json` selects all five proposition holes:
surjectivity of matrix reduction, commutativity of its kernel, independence of
kernel conjugation from the lift, the cocycle identity, and the main criterion.

The pinned GitHub workflow builds the proof, audits axioms, and invokes
Palomar's complete reusable verification workflow, including Comparator and
NanoDa. A preflight pass is distinct from Palomar editorial acceptance or
registration. See [workflow runs](https://github.com/AItoBit/DARPA-s-23-Mathematical-Challenges/actions).

## Sources and provenance

The precise result is the classical abelian-extension H² lifting obstruction,
specialized to general linear groups over a square-zero ring extension.
Its construction and complete proof are included here. The starting six
lemmas were supplied privately in the development conversation and have no
independent public publication identifier.

The supplied three-page `darpa-18.pdf` was read as motivation. Its SHA-256 is
`1ba91cec850556ea26625a3dc8c6eb3af0ec63d1aeef5abd440ed310929982a`.
The cited DARPA DSO BAA 07-68 Challenge Eighteen mirror
at `https://web.math.utk.edu/~vasili/refs/darpa07.MathChallenges.html`
returned 404 during the source audit. Neither that unavailable page nor the
research agenda is presented as a theorem proved by this repository.

Galatius and Venkatesh's [Derived Galois deformation rings](https://arxiv.org/abs/1608.07236)
provides related arithmetic context. No theorem of that paper is claimed to
be formalized. The substantive formal dependency is Mathlib's
[low-degree group cohomology](https://github.com/leanprover-community/mathlib4/blob/0db6cb99b412983de54b59ecc1b0b2747542cda3/Mathlib/RepresentationTheory/Homological/GroupCohomology/LowDegree.lean).
Structured provenance and AI disclosure are in `formalization.yaml`.

The repository's existing Apache-2.0 license applies to this development.
Sources and dependencies retain their own authorship and licenses.
