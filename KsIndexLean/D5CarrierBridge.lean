module

public import KsIndexLean.DiskTraceCovariance
public import KsIndexLean.DiskRotationForms
public import KsIndexLean.WeakBoundaryDomains
public import KsIndexLean.D5CharProjAlgebra
public import KsIndexLean.SingleDiskBridge

@[expose] public section


/-!
# Character averaging on the weak H¹ carrier

`carrierCharProj` is the finite ξ-weighted average of disk rotations, defined
as a continuous complex-linear map. It preserves convergence and, for positive
`k`, fixes the weak character sector of eigenvalue `ζ_k^r` by iterating its
rotation equation. This argument does not require a separate periodicity proof.

The value-coordinate identity identifies the average almost everywhere on the
disk with the corresponding weighted sum of rotated representatives. It does
not assert pointwise equality for arbitrary representatives of the L² classes.
-/

open Set MeasureTheory Filter Topology
open scoped ContDiff
noncomputable section
namespace KsIndex.Trace
open KsIndex.WeakH1 KsIndex.FormIndex KsIndex.SingleDiskBridge

/-- The paper's rotation angle `−2π/k` (the angle of `rotUnit k`). -/
def rotAngle (k : ℕ) : ℝ := -(2 * Real.pi) / k

/-- `planeRotation (j·θ_k)` is multiplication by `(rotUnit k)^j`. -/
lemma planeRotation_rotAngle_pow (k j : ℕ) (z : ℂ) :
    planeRotation ((j : ℝ) * rotAngle k) z =
      ((KsIndex.SurfaceSym.rotUnit k : Circle) : ℂ) ^ j * z := by
  rw [planeRotation_apply, KsIndex.SurfaceSym.rotUnit, Circle.coe_exp,
    ← Complex.exp_nat_mul]
  congr 2
  push_cast [rotAngle]
  ring

/-- **The carrier-side character projection**: the finite ξ-weighted
rotation average as a continuous linear map on the H¹ carrier. -/
def carrierCharProj (k r : ℕ) : ComplexH1 →L[ℂ] ComplexH1 :=
  (k : ℂ)⁻¹ • ∑ j ∈ Finset.range k, xi k ^ (r * j) •
    (diskRotation ((j : ℝ) * rotAngle k)).toContinuousLinearMap

lemma carrierCharProj_apply (k r : ℕ) (u : ComplexH1) :
    carrierCharProj k r u = (k : ℂ)⁻¹ • ∑ j ∈ Finset.range k,
      xi k ^ (r * j) • diskRotation ((j : ℝ) * rotAngle k) u := by
  simp [carrierCharProj]

/-- Continuity of character averaging preserves convergence in the H¹ carrier. -/
lemma carrierCharProj_tendsto (k r : ℕ) {f : ℕ → ComplexH1} {u : ComplexH1}
    (h : Tendsto f atTop (𝓝 u)) :
    Tendsto (fun n => carrierCharProj k r (f n)) atTop
      (𝓝 (carrierCharProj k r u)) :=
  ((carrierCharProj k r).continuous.tendsto u).comp h

/-- Iterating the character equation along the rotation group. -/
lemma diskRotation_iterate_of_char {k r : ℕ} {u : ComplexH1}
    (hu : diskRotation (rotAngle k) u = zeta k ^ r • u) :
    ∀ j : ℕ, diskRotation ((j : ℝ) * rotAngle k) u = (zeta k ^ r) ^ j • u
  | 0 => by
    have h0 : ((0 : ℕ) : ℝ) * rotAngle k = 0 := by push_cast; ring
    rw [h0, diskRotation_zero, pow_zero, one_smul]
  | j + 1 => by
    have hsplit : (((j + 1 : ℕ)) : ℝ) * rotAngle k =
        rotAngle k + (j : ℝ) * rotAngle k := by push_cast; ring
    rw [hsplit, diskRotation_add, diskRotation_iterate_of_char hu j, map_smul,
      hu, smul_smul, ← pow_succ]

/-- **The projection fixes the weak class-`r` sector.** -/
lemma carrierCharProj_eq_self {k r : ℕ} (hk : 0 < k) {u : ComplexH1}
    (hu : u ∈ weakCharacterDomain (rotAngle k) (zeta k ^ r)) :
    carrierCharProj k r u = u := by
  have hu' := (mem_weakCharacterDomain _ _ u).mp hu
  rw [carrierCharProj_apply]
  have h1 : ∀ j ∈ Finset.range k,
      xi k ^ (r * j) • diskRotation ((j : ℝ) * rotAngle k) u = u := by
    intro j _
    rw [diskRotation_iterate_of_char hu' j, ← pow_mul, smul_smul, mul_comm,
      zeta_pow_mul_xi_pow hk (r * j), one_smul]
  rw [Finset.sum_congr rfl h1, Finset.sum_const, Finset.card_range,
    ← Nat.cast_smul_eq_nsmul ℂ, smul_smul,
    inv_mul_cancel₀ (Nat.cast_ne_zero.mpr hk.ne'), one_smul]

/-- Finite `Lp` sums have a.e.-pointwise sums of representatives. -/
lemma lp_coeFn_finset_sum {ι : Type*} (s : Finset ι)
    (F : ι → Lp ℂ 2 (volume.restrict (disk : Set ℂ))) :
    ((∑ i ∈ s, F i : Lp ℂ 2 (volume.restrict (disk : Set ℂ))) : ℂ → ℂ)
      =ᵐ[volume.restrict (disk : Set ℂ)] fun z => ∑ i ∈ s, (F i : ℂ → ℂ) z := by
  classical
  induction s using Finset.induction with
  | empty =>
    simp only [Finset.sum_empty]
    filter_upwards [Lp.coeFn_zero (E := ℂ) (p := 2)
      (μ := volume.restrict (disk : Set ℂ))] with z hz
    simpa using hz
  | @insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    filter_upwards [Lp.coeFn_add (F a) (∑ i ∈ s, F i), ih] with z h1 h2
    rw [h1]
    simp only [Pi.add_apply, h2]

/-- The value coordinate of character averaging equals the ξ-weighted rotation
average of a value representative almost everywhere on the disk. -/
lemma carrierCharProj_value_ae (k r : ℕ) (u : ComplexH1) :
    (valueCLM (carrierCharProj k r u) : ℂ → ℂ)
      =ᵐ[volume.restrict (disk : Set ℂ)]
      fun z => (k : ℂ)⁻¹ • ∑ j ∈ Finset.range k, xi k ^ (r * j) •
        (valueCLM u : ℂ → ℂ)
          (((KsIndex.SurfaceSym.rotUnit k : Circle) : ℂ) ^ j * z) := by
  rw [carrierCharProj_apply, map_smul, map_sum]
  simp only [map_smul]
  have hae : ∀ j ∈ Finset.range k,
      ((valueCLM (diskRotation ((j : ℝ) * rotAngle k) u)) : ℂ → ℂ)
        =ᵐ[volume.restrict (disk : Set ℂ)]
        fun z => (valueCLM u : ℂ → ℂ)
          (((KsIndex.SurfaceSym.rotUnit k : Circle) : ℂ) ^ j * z) := by
    intro j _
    filter_upwards [diskRotation_value_ae ((j : ℝ) * rotAngle k) u] with z hz
    rw [hz, Function.comp_apply, planeRotation_rotAngle_pow]
  have hsum := lp_coeFn_finset_sum (Finset.range k)
    (fun j => xi k ^ (r * j) • valueCLM (diskRotation ((j : ℝ) * rotAngle k) u))
  have hterms : ∀ᵐ z ∂(volume.restrict (disk : Set ℂ)), ∀ j ∈ Finset.range k,
      ((xi k ^ (r * j) • valueCLM (diskRotation ((j : ℝ) * rotAngle k) u) :
        Lp ℂ 2 (volume.restrict (disk : Set ℂ))) : ℂ → ℂ) z =
        xi k ^ (r * j) • (valueCLM u : ℂ → ℂ)
          (((KsIndex.SurfaceSym.rotUnit k : Circle) : ℂ) ^ j * z) := by
    rw [Filter.eventually_all_finset]
    intro j hj
    filter_upwards [Lp.coeFn_smul (xi k ^ (r * j))
      (valueCLM (diskRotation ((j : ℝ) * rotAngle k) u)), hae j hj] with z h1 h2
    rw [h1, Pi.smul_apply, h2]
  filter_upwards [Lp.coeFn_smul ((k : ℂ)⁻¹)
      (∑ j ∈ Finset.range k, xi k ^ (r * j) •
        valueCLM (diskRotation ((j : ℝ) * rotAngle k) u)),
    hsum, hterms] with z h1 h2 h3
  rw [h1, Pi.smul_apply, h2]
  congr 1
  exact Finset.sum_congr rfl h3

end KsIndex.Trace
