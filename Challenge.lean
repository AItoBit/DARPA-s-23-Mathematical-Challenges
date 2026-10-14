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
# Square-zero representation lifting: challenge

For a surjective homomorphism of commutative rings whose kernel has square zero,
a discrete matrix representation lifts exactly when its H² obstruction vanishes.
The definitions below fix the action, cocycle and obstruction explicitly.
Proof holes specify supporting facts; Solution proves every one of them.
This classical obstruction theorem is not a solution of the DARPA-018 agenda.
-/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Darpa018.H2Core
variable {G M : Type}
variable [Group G] [AddCommGroup M] [DistribMulAction G M]
noncomputable def obstructionClass
    (c : G × G → M)
    (hc : groupCohomology.IsCocycle₂ c) :
    groupCohomology.H2 (Rep.ofDistribMulAction ℤ G M) :=
  (CategoryTheory.ConcreteCategory.hom
    (groupCohomology.H2π (Rep.ofDistribMulAction ℤ G M)))
    (groupCohomology.cocyclesOfIsCocycle₂ (k := ℤ) hc)

end Darpa018.H2Core

namespace Darpa018.MatrixSquareZero
universe u v w
variable {R : Type u} {S : Type v} {n : Type w}
variable [CommRing R] [CommRing S] [Fintype n] [DecidableEq n]

theorem units_map_surjective_of_squareZeroKernel
    (f : R →+* S) (hf : Function.Surjective f)
    (hsq : ∀ a b : R, f a = 0 → f b = 0 → a * b = 0) :
    Function.Surjective
      (Units.map (f.mapMatrix : Matrix n n R →+* Matrix n n S).toMonoidHom) := by sorry

theorem units_map_ker_isMulCommutative
    (f : R →+* S)
    (hsq : ∀ a b : R, f a = 0 → f b = 0 → a * b = 0) :
    IsMulCommutative
      (Units.map (f.mapMatrix : Matrix n n R →+* Matrix n n S).toMonoidHom).ker := by sorry

end Darpa018.MatrixSquareZero

namespace Darpa018.GroupExtension

open scoped IsMulCommutative

variable {G E Q : Type} [Group G] [Group E] [Group Q]
variable (q : E →* Q) [IsMulCommutative q.ker]

/-- Elements with equal images act identically on the abelian kernel. -/
theorem conj_eq_of_map_eq (a b : E) (hab : q a = q b) (x : q.ker) :
    a * x * a⁻¹ = b * x * b⁻¹ := by sorry

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
      _ = _ := by simp only [mul_inv_rev, mul_assoc]
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
    groupCohomology.IsCocycle₂ (defect q ρ l hl) := by sorry

/-- The second-cohomology obstruction defined by the defect of the chosen lifts. -/
noncomputable def obstruction :
    letI := kernelAction q ρ l hl
    groupCohomology.H2 (Rep.ofDistribMulAction ℤ G (Additive q.ker)) :=
  letI := kernelAction q ρ l hl
  H2Core.obstructionClass (defect q ρ l hl) (defect_isCocycle q ρ l hl)

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

end Darpa018.GroupExtension

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
      ∃ ρ' : G →* (Matrix n n R)ˣ, (reduction f).comp ρ' = ρ := by sorry

end Darpa018.RepresentationLifting
