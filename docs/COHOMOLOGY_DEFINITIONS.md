# Imported cohomology definitions

The complete pinned sources are included in [mathlib/](mathlib/) so that the
definitions can be read without fetching Mathlib or opening an external link.
These are unmodified source snapshots from Mathlib commit
`c55e6e786f49471c72fbddbec5415808896aec1e`, the revision in both
`lakefile.toml` and `lake-manifest.json`. The `.lean.txt` suffix marks them as
reference text. The project still imports Mathlib; it does not compile a
second copy of these declarations.

The original copyright and author headers are preserved. Mathlib's
[Apache-2.0 license](mathlib/LICENSE.txt) accompanies the copies.
[manifest.json](mathlib/manifest.json) records each upstream path, immutable
raw URL and SHA-256. CI compares every snapshot byte for byte with the Git
blob in the pinned Mathlib checkout:

```sh
python3 scripts/check_mathlib_sources.py
```

## Definition chain

Line numbers below refer to the complete snapshots, without an added header.
All `LowDegree` declarations are in namespace `groupCohomology`.

| Mathematical object | Source and declarations |
| --- | --- |
| Coefficient representation with the given action | [Rep.Basic.lean.txt](mathlib/Rep.Basic.lean.txt), lines 355–364: `Rep.ofDistribMulAction` and `ofDistribMulAction_ρ_apply_apply`. The latter is proved by `rfl`: the representation sends `g, a` to `g • a`. |
| Ordinary inhomogeneous cochain complex | [GroupCohomology.Basic.lean.txt](mathlib/GroupCohomology.Basic.lean.txt), lines 83–126: `inhomogeneousCochains.d` and `inhomogeneousCochains`. Cochains are functions `(Fin n → G) → A`; the differential is the usual alternating sum with the action in its first term. |
| Group cohomology and its projection | [GroupCohomology.Basic.lean.txt](mathlib/GroupCohomology.Basic.lean.txt), lines 183–193: `groupCohomology A n` is `(inhomogeneousCochains A).homology n`; `groupCohomology.π` is its homology projection. |
| Explicit differentials in degrees one and two | [LowDegree.lean.txt](mathlib/LowDegree.lean.txt), lines 119–146: `d₁₂` and `d₂₃`. Lines 194–236 prove `comp_d₁₂_eq` and `comp_d₂₃_eq`, identifying these formulas with the cochain differential. |
| Cocycles and coboundaries | [LowDegree.lean.txt](mathlib/LowDegree.lean.txt), lines 277–281 and 413–417: `cocycles₂` is `ker d₂₃`; `coboundaries₂` is `range d₁₂`. |
| The predicates used by this project | [LowDegree.lean.txt](mathlib/LowDegree.lean.txt), lines 494–499 and 545–549: `IsCocycle₂` and `IsCoboundary₂`. Lines 585–611 provide `cocyclesOfIsCocycle₂`, `coboundariesOfIsCoboundary₂` and their reverse implications. |
| Identification with ordinary second cohomology | [LowDegree.lean.txt](mathlib/LowDegree.lean.txt), lines 858–874 and 1041–1094: `isoShortComplexH2`, `H2`, `H2π`, `H2π_eq_zero_iff` and `H2Iso`. |
| Concrete quotient underlying module homology | [ShortComplex.ModuleCat.lean.txt](mathlib/ShortComplex.ModuleCat.lean.txt), lines 96–110: `moduleCatLeftHomologyData` takes the kernel of the second map and quotients by the range of the first map restricted to that kernel. |

## Formulas and correspondence

Write the coefficient action as $g\cdot a$. The pinned definitions give

$$
(d^1 b)(g,h)=g\cdot b(h)-b(gh)+b(g),
$$

$$
(d^2 c)(g,h,j)=g\cdot c(h,j)-c(gh,j)+c(g,hj)-c(g,h).
$$

`IsCocycle₂ c` is exactly

```lean
∀ g h j : G, c (g * h, j) + c (g, h) = g • c (h, j) + c (g, h * j)
```

`IsCoboundary₂ c` is exactly

```lean
∃ b : G → A, ∀ g h : G, g • b h - b (g * h) + b g = c (g, h)
```

Thus the predicates express $d^2c=0$ and $c=d^1b$. These are ordinary
inhomogeneous cochains; no normalization at the identity is imposed.
`H2Iso` identifies `H2 A` with the concrete quotient of these cocycles by
these coboundaries. `H2π` maps a cocycle to its class, and
`H2π_eq_zero_iff` states that the class vanishes exactly for a coboundary.
These identifications are proved in the included source, rather than inferred
from declaration names.

In [Challenge.lean](../Challenge.lean), `Darpa018.H2Core.obstructionClass`
applies `H2π` to `cocyclesOfIsCocycle₂ hc`. The matrix obstruction specializes
this construction to `A = Additive (reduction f).ker` over `ℤ`, with
`kernelAction` induced by conjugation by chosen lifts. The coefficient group
is this additive kernel, and the action can be nontrivial.
The cocycle is the additive type-tag of `l(g) l(h) l(gh)⁻¹`.

In [Solution.lean](../Solution.lean),
`Darpa018.H2Core.obstructionClass_zero_iff_coboundary` applies
`H2π_eq_zero_iff` and the two predicate conversions above.
`hasSection_iff_isCoboundary₂` then relates this condition to the explicit
section equation. The subsequent lifting theorems use this criterion.
The snapshots supply dependency definitions for inspection; the proof and
Comparator targets remain those of the original development.
