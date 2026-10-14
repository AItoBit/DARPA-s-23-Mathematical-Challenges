module

public import Mathlib.RepresentationTheory.Homological.GroupCohomology.LowDegree
public import Mathlib.Tactic.Abel
public import Mathlib.Data.Matrix.Basic
public import Mathlib.Algebra.Group.Units.Hom
public import Mathlib.Algebra.Group.Subgroup.Ker
public import Mathlib.Tactic.NoncommRing
public import Mathlib.GroupTheory.GroupAction.ConjAct
public import Mathlib.Tactic.Group
public import Mathlib.RingTheory.Ideal.Maps
public import Mathlib.Algebra.Group.TypeTags.Basic

/-!
# DARPA-018: cohomology and discrete representation lifting

This file proves the six lemmas supplied by the user and the resulting
square-zero representation-lifting obstruction theorem. The main declaration is
`Darpa018.RepresentationLifting.obstruction_zero_iff_lift`.

The underlying additive coefficient group is identified with matrices over the
coefficient-ring kernel by `Darpa018.KernelIdentification.coefficientAddEquiv`.

Sources: the user's H2 and matrix lemmas; Mathlib's low-degree group cohomology
and conjugation APIs. The supplied `darpa-18.pdf` motivates the work, but describes
a research agenda, not a single proposition. No Langlands correspondence,
arithmetic comparison, or statement about continuous representations is asserted.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false
/-!
# Second-cohomology obstruction to solving the section equation

For a group action on an additive commutative group, the equation
`t (g * h) = t g + g • t h + c (g, h)` has a solution exactly when `c` is a
2-coboundary. For a 2-cocycle, this is equivalent to its class in `H²` vanishing.

The cohomology definitions and sign convention are those of Mathlib's
`RepresentationTheory.Homological.GroupCohomology.LowDegree`.
-/

namespace Darpa018.H2Core

variable {G M : Type}
variable [Group G] [AddCommGroup M] [DistribMulAction G M]

/-- The section equation associated to the function `c` has a solution. -/
def HasSection (c : G × G → M) : Prop :=
  ∃ t : G → M, ∀ g h,
    t (g * h) = t g + g • t h + c (g, h)

/-- The section equation has a solution exactly when `c` is a 2-coboundary. -/
theorem hasSection_iff_isCoboundary₂
    (c : G × G → M) :
    HasSection c ↔ groupCohomology.IsCoboundary₂ c := by
  constructor
  · rintro ⟨t, ht⟩
    refine ⟨fun g => -t g, ?_⟩
    intro g h
    change g • (-t h) - (-t (g * h)) + (-t g) = c (g, h)
    rw [smul_neg]
    calc
      -(g • t h) - (-t (g * h)) + (-t g) =
          t (g * h) - (t g + g • t h) := by abel
      _ = c (g, h) := by rw [ht g h]; abel
  · rintro ⟨s, hs⟩
    refine ⟨fun g => -s g, ?_⟩
    intro g h
    change -s (g * h) = -s g + g • (-s h) + c (g, h)
    rw [smul_neg, ← hs g h]
    abel

/-- The second-cohomology class of `c`, with coefficients in `M` as a `ℤ`-module. -/
noncomputable def obstructionClass
    (c : G × G → M)
    (hc : groupCohomology.IsCocycle₂ c) :
    groupCohomology.H2 (Rep.ofDistribMulAction ℤ G M) :=
  (CategoryTheory.ConcreteCategory.hom
    (groupCohomology.H2π (Rep.ofDistribMulAction ℤ G M)))
    (groupCohomology.cocyclesOfIsCocycle₂ (k := ℤ) hc)

/-- A cocycle has zero cohomology class exactly when it is a coboundary. -/
theorem obstructionClass_zero_iff_coboundary
    (c : G × G → M)
    (hc : groupCohomology.IsCocycle₂ c) :
    obstructionClass c hc = 0 ↔ groupCohomology.IsCoboundary₂ c := by
  unfold obstructionClass
  rw [groupCohomology.H2π_eq_zero_iff]
  constructor
  · intro h
    exact groupCohomology.isCoboundary₂_of_mem_coboundaries₂ (k := ℤ) c h
  · intro h
    exact (groupCohomology.coboundariesOfIsCoboundary₂ (k := ℤ) h).property

/-- A cocycle has zero cohomology class exactly when its section equation is solvable. -/
theorem obstructionClass_zero_iff_section
    (c : G × G → M)
    (hc : groupCohomology.IsCocycle₂ c) :
    obstructionClass c hc = 0 ↔ HasSection c := by
  rw [obstructionClass_zero_iff_coboundary c hc]
  exact (hasSection_iff_isCoboundary₂ c).symm

end Darpa018.H2Core

/-!
# Square-zero matrix lemmas

The starting statements and explicit inverse construction were supplied by the user.
These are algebraic ingredients motivated by DARPA Mathematical Challenge 18,
not a formulation of that research programme.
-/

namespace Darpa018.MatrixSquareZero

universe u v w

variable {R : Type u} {S : Type v} {n : Type w}
variable [CommRing R] [CommRing S] [Fintype n]

/-- Matrices whose entries lie in a square-zero kernel multiply to zero. -/
theorem mul_eq_zero_of_map_eq_zero
    (f : R →+* S)
    (hsq : ∀ a b : R, f a = 0 → f b = 0 → a * b = 0)
    (A B : Matrix n n R)
    (hA : A.map f = 0)
    (hB : B.map f = 0) :
    A * B = 0 := by
  classical
  ext i j
  rw [Matrix.mul_apply]
  apply Finset.sum_eq_zero
  intro k _
  apply hsq
  · have h := congrArg (fun C : Matrix n n S => C i k) hA
    simpa using h
  · have h := congrArg (fun C : Matrix n n S => C k j) hB
    simpa using h

variable [DecidableEq n]

/-- An approximate inverse with square-zero defects yields an actual inverse. -/
theorem isUnit_of_square_zero_defects
    (A B : Matrix n n R)
    (hAB : (1 - A * B) * (1 - A * B) = 0)
    (hBA : (1 - B * A) * (1 - B * A) = 0) :
    IsUnit A := by
  let E : Matrix n n R := 1 - A * B
  let F : Matrix n n R := 1 - B * A
  let C : Matrix n n R := B * (1 + E)
  let D : Matrix n n R := (1 + F) * B
  have hright : A * C = 1 := by
    change A * (B * (1 + (1 - A * B))) = 1
    calc
      A * (B * (1 + (1 - A * B))) =
          1 - (1 - A * B) * (1 - A * B) := by noncomm_ring
      _ = 1 := by rw [hAB]; simp
  have hleft : D * A = 1 := by
    change ((1 + (1 - B * A)) * B) * A = 1
    calc
      ((1 + (1 - B * A)) * B) * A =
          1 - (1 - B * A) * (1 - B * A) := by noncomm_ring
      _ = 1 := by rw [hBA]; simp
  have hDC : D = C := by
    calc
      D = D * (A * C) := by rw [hright, mul_one]
      _ = (D * A) * C := (mul_assoc D A C).symm
      _ = C := by rw [hleft, one_mul]
  have hClef : C * A = 1 := by
    rw [← hDC]
    exact hleft
  exact ⟨{ val := A, inv := C, val_inv := hright, inv_val := hClef }, rfl⟩

/-- Approximate inverses modulo a square-zero kernel lift to actual inverses. -/
theorem isUnit_of_squareZeroKernel_approxInverse
    (f : R →+* S)
    (hsq : ∀ a b : R, f a = 0 → f b = 0 → a * b = 0)
    (A B : Matrix n n R)
    (hAB : (1 - A * B).map f = 0)
    (hBA : (1 - B * A).map f = 0) :
    IsUnit A := by
  have h1 : (1 - A * B) * (1 - A * B) = 0 :=
    mul_eq_zero_of_map_eq_zero f hsq _ _ hAB hAB
  have h2 : (1 - B * A) * (1 - B * A) = 0 :=
    mul_eq_zero_of_map_eq_zero f hsq _ _ hBA hBA
  exact isUnit_of_square_zero_defects A B h1 h2

omit [Fintype n] [DecidableEq n] in
/-- A surjective map of coefficients is surjective on matrices. -/
theorem map_surjective (f : R →+* S) (hf : Function.Surjective f) :
    Function.Surjective (fun A : Matrix n n R => A.map f) := by
  classical
  intro A
  choose b hb using fun i j => hf (A i j)
  exact ⟨b, funext fun i => funext fun j => hb i j⟩

/-- A matrix is invertible exactly when its reduction is invertible, provided the
coefficient map is surjective with square-zero kernel. -/
theorem isUnit_map_iff_of_squareZeroKernel
    (f : R →+* S) (hf : Function.Surjective f)
    (hsq : ∀ a b : R, f a = 0 → f b = 0 → a * b = 0)
    (A : Matrix n n R) :
    IsUnit (A.map f) ↔ IsUnit A := by
  constructor
  · rintro ⟨u, hu⟩
    obtain ⟨B, hB⟩ := map_surjective (n := n) f hf (↑(u⁻¹))
    change B.map f = (↑(u⁻¹) : Matrix n n S) at hB
    apply isUnit_of_squareZeroKernel_approxInverse f hsq A B
    · change f.mapMatrix (1 - A * B) = 0
      rw [map_sub, map_one, map_mul]
      change 1 - A.map f * B.map f = 0
      rw [hB, ← hu, Units.mul_inv, sub_self]
    · change f.mapMatrix (1 - B * A) = 0
      rw [map_sub, map_one, map_mul]
      change 1 - B.map f * A.map f = 0
      rw [hB, ← hu, Units.inv_mul, sub_self]
  · exact fun h => h.map f.mapMatrix

/-- Reduction on general linear groups is surjective for a surjective coefficient
map with square-zero kernel. -/
theorem units_map_surjective_of_squareZeroKernel
    (f : R →+* S) (hf : Function.Surjective f)
    (hsq : ∀ a b : R, f a = 0 → f b = 0 → a * b = 0) :
    Function.Surjective
      (Units.map (f.mapMatrix : Matrix n n R →+* Matrix n n S).toMonoidHom) := by
  intro u
  obtain ⟨A, hA⟩ := map_surjective (n := n) f hf (↑u)
  change A.map f = (↑u : Matrix n n S) at hA
  have hunit : IsUnit A :=
    (isUnit_map_iff_of_squareZeroKernel f hf hsq A).mp (hA.symm ▸ u.isUnit)
  obtain ⟨v, hv⟩ := hunit
  refine ⟨v, Units.ext ?_⟩
  change (↑v : Matrix n n R).map f = ↑u
  rw [hv, hA]

/-- Two invertible matrices reducing to the identity commute when the coefficient
kernel has square zero. -/
theorem units_commute_of_map_eq_one
    (f : R →+* S)
    (hsq : ∀ a b : R, f a = 0 → f b = 0 → a * b = 0)
    (u v : (Matrix n n R)ˣ)
    (hu : Units.map f.mapMatrix.toMonoidHom u = 1)
    (hv : Units.map f.mapMatrix.toMonoidHom v = 1) :
    Commute u v := by
  have hu' : (↑u : Matrix n n R).map f = 1 := congrArg Units.val hu
  have hv' : (↑v : Matrix n n R).map f = 1 := congrArg Units.val hv
  have hU : ((↑u : Matrix n n R) - 1).map f = 0 := by
    change f.mapMatrix ((↑u : Matrix n n R) - 1) = 0
    rw [map_sub, map_one]
    exact sub_eq_zero.mpr hu'
  have hV : ((↑v : Matrix n n R) - 1).map f = 0 := by
    change f.mapMatrix ((↑v : Matrix n n R) - 1) = 0
    rw [map_sub, map_one]
    exact sub_eq_zero.mpr hv'
  have hUV := mul_eq_zero_of_map_eq_zero f hsq _ _ hU hV
  have hVU := mul_eq_zero_of_map_eq_zero f hsq _ _ hV hU
  change u * v = v * u
  apply Units.ext
  change (↑u : Matrix n n R) * (↑v : Matrix n n R) =
    (↑v : Matrix n n R) * (↑u : Matrix n n R)
  calc
    (↑u : Matrix n n R) * (↑v : Matrix n n R) =
        ((↑u : Matrix n n R) - 1) * ((↑v : Matrix n n R) - 1) +
          (↑u : Matrix n n R) + (↑v : Matrix n n R) - 1 := by noncomm_ring
    _ = ((↑v : Matrix n n R) - 1) * ((↑u : Matrix n n R) - 1) +
          (↑v : Matrix n n R) + (↑u : Matrix n n R) - 1 := by rw [hUV, hVU]; abel
    _ = (↑v : Matrix n n R) * (↑u : Matrix n n R) := by noncomm_ring

/-- The kernel of reduction on general linear groups is abelian. -/
theorem units_map_ker_isMulCommutative
    (f : R →+* S)
    (hsq : ∀ a b : R, f a = 0 → f b = 0 → a * b = 0) :
    IsMulCommutative
      (Units.map (f.mapMatrix : Matrix n n R →+* Matrix n n S).toMonoidHom).ker := by
  rw [isMulCommutative_iff]
  intro u v
  apply Subtype.ext
  exact units_commute_of_map_eq_one (n := n) f hsq u.val v.val u.property v.property

end Darpa018.MatrixSquareZero

/-!
# The obstruction to lifting a homomorphism through an abelian group extension

For a surjective homomorphism with abelian kernel, conjugation defines an action
on the additive kernel. The defect of chosen lifts is a 2-cocycle. Its class
vanishes exactly when the original homomorphism has a homomorphic lift.
-/

namespace Darpa018.GroupExtension

open scoped IsMulCommutative

variable {G E Q : Type} [Group G] [Group E] [Group Q]
variable (q : E →* Q) [IsMulCommutative q.ker]

/-- Elements with equal images act identically on the abelian kernel. -/
theorem conj_eq_of_map_eq (a b : E) (hab : q a = q b) (x : q.ker) :
    a * x * a⁻¹ = b * x * b⁻¹ := by
  let k : q.ker := ⟨b⁻¹ * a, by simp [MonoidHom.mem_ker, hab]⟩
  have hk : (b⁻¹ * a) * (x : E) = (x : E) * (b⁻¹ * a) :=
    congrArg (fun y : q.ker => (y : E)) (mul_comm k x)
  calc
    a * x * a⁻¹ = b * ((b⁻¹ * a) * x) * a⁻¹ := by group
    _ = b * (x * (b⁻¹ * a)) * a⁻¹ := by rw [hk]
    _ = b * x * b⁻¹ := by group

variable (ρ : G →* Q) (l : G → E) (hl : ∀ g, q (l g) = ρ g)

/-- The induced action on the additive kernel, calculated using chosen lifts. -/
abbrev kernelAction : DistribMulAction G (Additive q.ker) where
  smul g x := Additive.ofMul (MulAut.conjNormal (l g) x.toMul)
  one_smul x := by
    apply Additive.toMul.injective
    apply Subtype.ext
    change l 1 * (x.toMul : E) * (l 1)⁻¹ = (x.toMul : E)
    simpa using conj_eq_of_map_eq q (l 1) 1 (by simp [hl]) x.toMul
  mul_smul g h x := by
    apply Additive.toMul.injective
    apply Subtype.ext
    change l (g * h) * (x.toMul : E) * (l (g * h))⁻¹ =
      l g * (l h * (x.toMul : E) * (l h)⁻¹) * (l g)⁻¹
    calc
      _ = (l g * l h) * (x.toMul : E) * (l g * l h)⁻¹ :=
        conj_eq_of_map_eq q _ _ (by simp [hl]) _
      _ = _ := by group
  smul_zero g := by
    apply Additive.toMul.injective
    exact map_one (MulAut.conjNormal (l g))
  smul_add g x y := by
    apply Additive.toMul.injective
    exact map_mul (MulAut.conjNormal (l g)) x.toMul y.toMul

/-- The defect of multiplicativity of the chosen lifts, as an additive cochain. -/
def defect (p : G × G) : Additive q.ker :=
  Additive.ofMul ⟨l p.1 * l p.2 * (l (p.1 * p.2))⁻¹,
    by simp [MonoidHom.mem_ker, hl]⟩



/-- Associativity makes the defect a 2-cocycle. -/
theorem defect_isCocycle :
    letI := kernelAction q ρ l hl
    groupCohomology.IsCocycle₂ (defect q ρ l hl) := by
  let := kernelAction q ρ l hl
  intro g h j
  apply Additive.toMul.injective
  change (defect q ρ l hl (g * h, j)).toMul * (defect q ρ l hl (g, h)).toMul = _
  rw [mul_comm (defect q ρ l hl (g * h, j)).toMul]
  apply Subtype.ext
  change (l g * l h * (l (g * h))⁻¹) *
      (l (g * h) * l j * (l ((g * h) * j))⁻¹) =
    (l g * (l h * l j * (l (h * j))⁻¹) * (l g)⁻¹) *
      (l g * l (h * j) * (l (g * (h * j)))⁻¹)
  rw [mul_assoc g h j]
  group

/-- Solutions of the section equation are exactly homomorphic lifts. -/
theorem hasSection_iff_lift :
    letI := kernelAction q ρ l hl
    H2Core.HasSection (defect q ρ l hl) ↔ ∃ f : G →* E, q.comp f = ρ := by
  let := kernelAction q ρ l hl
  constructor
  · rintro ⟨t, ht⟩
    let F : G → E := fun g => (t g).toMul * l g
    have hF (g h : G) : F (g * h) = F g * F h := by
      have heq := congrArg (fun z : Additive q.ker => (z.toMul : E)) (ht g h)
      change ((t (g * h)).toMul : E) =
        ((t g).toMul * (l g * (t h).toMul * (l g)⁻¹)) *
          (l g * l h * (l (g * h))⁻¹) at heq
      change ((t (g * h)).toMul : E) * l (g * h) =
        ((t g).toMul * l g) * ((t h).toMul * l h)
      rw [heq]
      group
    refine ⟨MonoidHom.mk' F hF, ?_⟩
    ext g
    change q ((t g).toMul * l g) = ρ g
    rw [map_mul, (t g).toMul.property, one_mul, hl]
  · rintro ⟨f, hf⟩
    have hfg (g : G) : q (f g) = ρ g := DFunLike.congr_fun hf g
    let t : G → Additive q.ker := fun g =>
      Additive.ofMul ⟨f g * (l g)⁻¹, by simp [MonoidHom.mem_ker, hfg, hl]⟩
    refine ⟨t, ?_⟩
    intro g h
    apply Additive.toMul.injective
    apply Subtype.ext
    change f (g * h) * (l (g * h))⁻¹ =
      (f g * (l g)⁻¹ * (l g * (f h * (l h)⁻¹) * (l g)⁻¹)) *
        (l g * l h * (l (g * h))⁻¹)
    rw [map_mul]
    group

/-- The second-cohomology obstruction defined by the defect of the chosen lifts. -/
noncomputable def obstruction :
    letI := kernelAction q ρ l hl
    groupCohomology.H2 (Rep.ofDistribMulAction ℤ G (Additive q.ker)) :=
  letI := kernelAction q ρ l hl
  H2Core.obstructionClass (defect q ρ l hl) (defect_isCocycle q ρ l hl)

/-- The obstruction vanishes exactly when the homomorphism admits a homomorphic lift. -/
theorem obstruction_zero_iff_lift :
    obstruction q ρ l hl = 0 ↔ ∃ f : G →* E, q.comp f = ρ := by
  let := kernelAction q ρ l hl
  rw [obstruction, H2Core.obstructionClass_zero_iff_section]
  exact hasSection_iff_lift q ρ l hl

/-- Vanishing of the obstruction is independent of the chosen pointwise lifts. -/
theorem obstruction_zero_iff_of_lifts (l' : G → E) (hl' : ∀ g, q (l' g) = ρ g) :
    obstruction q ρ l hl = 0 ↔ obstruction q ρ l' hl' = 0 := by
  rw [obstruction_zero_iff_lift, obstruction_zero_iff_lift]

/-- Chosen preimages of a homomorphism under a surjective homomorphism. -/
noncomputable def chosenLift (hq : Function.Surjective q) (g : G) : E :=
  Function.surjInv hq (ρ g)

omit [IsMulCommutative q.ker] in
/-- The chosen preimages lift the homomorphism pointwise. -/
theorem chosenLift_spec (hq : Function.Surjective q) (g : G) :
    q (chosenLift q ρ hq g) = ρ g :=
  Function.surjInv_eq hq (ρ g)

/-- The induced action for the chosen preimages of a surjective homomorphism. -/
noncomputable abbrev liftingAction (hq : Function.Surjective q) :
    DistribMulAction G (Additive q.ker) :=
  kernelAction q ρ (chosenLift q ρ hq) (chosenLift_spec q ρ hq)

/-- The obstruction to lifting `ρ` through the surjection `q` with abelian kernel. -/
noncomputable def liftingObstruction (hq : Function.Surjective q) :
    letI := liftingAction q ρ hq
    groupCohomology.H2 (Rep.ofDistribMulAction ℤ G (Additive q.ker)) :=
  obstruction q ρ (chosenLift q ρ hq) (chosenLift_spec q ρ hq)

/-- A homomorphism lifts through a surjection with abelian kernel if and only if
its second-cohomology obstruction vanishes. -/
theorem liftingObstruction_zero_iff_lift (hq : Function.Surjective q) :
    liftingObstruction q ρ hq = 0 ↔ ∃ f : G →* E, q.comp f = ρ :=
  obstruction_zero_iff_lift q ρ (chosenLift q ρ hq) (chosenLift_spec q ρ hq)

end Darpa018.GroupExtension

/-!
# Coefficients of a square-zero matrix lifting obstruction

The kernel of reduction on invertible matrices is additively identified with
the kernel of the matrix ring homomorphism. The maps are $u \mapsto u-1$ and
$X \mapsto 1+X$. This is an algebraic ingredient in representation lifting.
-/

namespace Darpa018.KernelIdentification

universe u v w

variable {R : Type u} {S : Type v} {n : Type w}
variable [CommRing R] [CommRing S] [Fintype n] [DecidableEq n]

abbrev reduction (f : R →+* S) : (Matrix n n R)ˣ →* (Matrix n n S)ˣ :=
  Units.map (f.mapMatrix : Matrix n n R →+* Matrix n n S).toMonoidHom

/-- Subtracting the identity places an element of the group kernel in the ring kernel. -/
def toRingKernel (f : R →+* S) (u : Additive (reduction (n := n) f).ker) :
    RingHom.ker (f.mapMatrix : Matrix n n R →+* Matrix n n S) := by
  refine ⟨(u.toMul.val : Matrix n n R) - 1, ?_⟩
  rw [RingHom.mem_ker, map_sub, map_one]
  have hu : reduction (n := n) f u.toMul.val = 1 := u.toMul.property
  exact sub_eq_zero.mpr (congrArg Units.val hu)

/-- A matrix in a square-zero kernel gives the unit $1+X$, with inverse $1-X$. -/
def fromRingKernel (f : R →+* S)
    (hsq : ∀ a b : R, f a = 0 → f b = 0 → a * b = 0)
    (X : RingHom.ker (f.mapMatrix : Matrix n n R →+* Matrix n n S)) :
    Additive (reduction (n := n) f).ker := by
  have hx : (X.val : Matrix n n R).map f = 0 := X.property
  have hxx : (X.val : Matrix n n R) * X.val = 0 :=
    MatrixSquareZero.mul_eq_zero_of_map_eq_zero f hsq _ _ hx hx
  let v : (Matrix n n R)ˣ :=
    { val := 1 + X.val
      inv := 1 - X.val
      val_inv := by
        calc
          (1 + X.val) * (1 - X.val) = 1 - X.val * X.val := by noncomm_ring
          _ = 1 := by rw [hxx, sub_zero]
      inv_val := by
        calc
          (1 - X.val) * (1 + X.val) = 1 - X.val * X.val := by noncomm_ring
          _ = 1 := by rw [hxx, sub_zero] }
  refine Additive.ofMul ⟨v, ?_⟩
  apply Units.ext
  change f.mapMatrix (1 + X.val) = 1
  rw [map_add, map_one]
  change 1 + (X.val : Matrix n n R).map f = 1
  rw [hx, add_zero]

/-- Reduction-kernel units form the additive group of matrices in the coefficient kernel. -/
def kernelAddEquiv (f : R →+* S)
    (hsq : ∀ a b : R, f a = 0 → f b = 0 → a * b = 0) :
    Additive (reduction (n := n) f).ker ≃+
      RingHom.ker (f.mapMatrix : Matrix n n R →+* Matrix n n S) where
  toFun := toRingKernel f
  invFun := fromRingKernel f hsq
  left_inv u := by
    apply Additive.ext
    apply Subtype.ext
    apply Units.ext
    change 1 + ((u.toMul.val : Matrix n n R) - 1) = u.toMul.val
    abel
  right_inv X := by
    apply Subtype.ext
    change (1 + (X.val : Matrix n n R)) - 1 = X.val
    abel
  map_add' u v := by
    apply Subtype.ext
    change (u.toMul.val : Matrix n n R) * v.toMul.val - 1 =
      ((u.toMul.val : Matrix n n R) - 1) + ((v.toMul.val : Matrix n n R) - 1)
    have hu : ((u.toMul.val : Matrix n n R) - 1).map f = 0 :=
      (toRingKernel f u).property
    have hv : ((v.toMul.val : Matrix n n R) - 1).map f = 0 :=
      (toRingKernel f v).property
    have huv := MatrixSquareZero.mul_eq_zero_of_map_eq_zero f hsq _ _ hu hv
    calc
      (u.toMul.val : Matrix n n R) * v.toMul.val - 1 =
          ((u.toMul.val : Matrix n n R) - 1) * ((v.toMul.val : Matrix n n R) - 1) +
            (((u.toMul.val : Matrix n n R) - 1) + ((v.toMul.val : Matrix n n R) - 1)) := by
        noncomm_ring
      _ = _ := by rw [huv, zero_add]

/-- The matrix ring kernel consists exactly of matrices with entries in the coefficient kernel. -/
def matrixKernelAddEquiv (f : R →+* S) :
    RingHom.ker (f.mapMatrix : Matrix n n R →+* Matrix n n S) ≃+
      Matrix n n (RingHom.ker f) where
  toFun X i j := ⟨X.val i j, by
    have hx : (X.val : Matrix n n R).map f = 0 := X.property
    exact congrArg (fun A : Matrix n n S => A i j) hx⟩
  invFun X := ⟨fun i j => (X i j).val, by
    change f.mapMatrix (fun i j => (X i j).val) = 0
    ext i j
    exact (X i j).property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl

/-- The abelian kernel of general linear reduction is the group of matrices over $\ker f$. -/
def coefficientAddEquiv (f : R →+* S)
    (hsq : ∀ a b : R, f a = 0 → f b = 0 → a * b = 0) :
    Additive (reduction (n := n) f).ker ≃+ Matrix n n (RingHom.ker f) :=
  (kernelAddEquiv f hsq).trans (matrixKernelAddEquiv f)

/-- The coefficient identification sends an invertible matrix to its difference from identity. -/
@[simp] theorem coefficientAddEquiv_apply (f : R →+* S)
    (hsq : ∀ a b : R, f a = 0 → f b = 0 → a * b = 0)
    (u : Additive (reduction (n := n) f).ker) (i j : n) :
    ((coefficientAddEquiv f hsq u) i j).val =
      ((u.toMul.val : Matrix n n R) - 1) i j := rfl

end Darpa018.KernelIdentification

/-!
# The obstruction to lifting a discrete matrix representation

For a surjective homomorphism of commutative rings with square-zero kernel,
a representation in invertible matrices lifts precisely when its explicit
second-cohomology obstruction vanishes.

The coefficient group is the additive form of the kernel of reduction on
invertible matrices. Its action is induced by conjugation through chosen lifts.
No topology or continuity is assumed.
-/

namespace Darpa018.RepresentationLifting

open scoped IsMulCommutative

variable {G R S n : Type} [Group G] [CommRing R] [CommRing S]
variable [Fintype n] [DecidableEq n]

/-- Reduction of invertible matrices along a homomorphism of coefficient rings. -/
abbrev reduction (f : R →+* S) : (Matrix n n R)ˣ →* (Matrix n n S)ˣ :=
  Units.map f.mapMatrix.toMonoidHom

variable (f : R →+* S) (hf : Function.Surjective f)
variable (hsq : ∀ a b : R, f a = 0 → f b = 0 → a * b = 0)
variable (ρ : G →* (Matrix n n S)ˣ)

/-- The action on the additive kernel induced by the representation. -/
noncomputable abbrev coefficientAction :
    letI := MatrixSquareZero.units_map_ker_isMulCommutative (n := n) f hsq
    DistribMulAction G (Additive (reduction (n := n) f).ker) :=
  letI := MatrixSquareZero.units_map_ker_isMulCommutative (n := n) f hsq
  GroupExtension.liftingAction (reduction f) ρ
    (MatrixSquareZero.units_map_surjective_of_squareZeroKernel f hf hsq)

/-- The second-cohomology obstruction to lifting the matrix representation. -/
noncomputable def obstruction :
    letI := MatrixSquareZero.units_map_ker_isMulCommutative (n := n) f hsq
    letI := coefficientAction f hf hsq ρ
    groupCohomology.H2
      (Rep.ofDistribMulAction ℤ G (Additive (reduction (n := n) f).ker)) :=
  letI := MatrixSquareZero.units_map_ker_isMulCommutative (n := n) f hsq
  GroupExtension.liftingObstruction (reduction f) ρ
    (MatrixSquareZero.units_map_surjective_of_squareZeroKernel f hf hsq)

/-- A discrete representation lifts across a surjective ring homomorphism with
square-zero kernel if and only if its second-cohomology obstruction vanishes. -/
theorem obstruction_zero_iff_lift :
    obstruction f hf hsq ρ = 0 ↔
      ∃ ρ' : G →* (Matrix n n R)ˣ, (reduction f).comp ρ' = ρ := by
  let := MatrixSquareZero.units_map_ker_isMulCommutative (n := n) f hsq
  exact GroupExtension.liftingObstruction_zero_iff_lift (reduction f) ρ
    (MatrixSquareZero.units_map_surjective_of_squareZeroKernel f hf hsq)

end Darpa018.RepresentationLifting
