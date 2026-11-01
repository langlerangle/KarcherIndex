module

/-
KsIndexLean — ZeroMeanProjection: the angular average `P₀` on the weak H¹
disk carrier ([ksindexi] tex 1810–1838: the rotation-invariant subspace
`H¹_{S¹}(S²₋)` and its zero-angular-mean complement `H¹_{(0;k),⊥}`).

`P₀ u = (2π)⁻¹ • ∫₀^{2π} R_θ u dθ` (carrier-valued Bochner integral;
`R_θ = diskRotation θ` is a linear isometry). The module proves
2π-periodicity of the action, rotation invariance and idempotence of the
average, and the range characterization by invariance under every rotation.
This is stronger than invariance under a finite cyclic group, which allows
nonzero angular frequencies divisible by `k`. The average is bundled as a
continuous complex-linear map of norm at most one; its kernel defines the
zero-angular-mean domain within the class-zero sector.

Downstream files supply the trace/extension bridges and the `nop-sphop`
zero-mean block transport.  (`diskAngularProjection 0` is the same average
through `fourierCoeffOn`; that spelling carries a different ℝ-normed-space
instance on the integral, so this file states `P₀` directly as an interval
Bochner integral and derives everything against that single spelling.)
-/
public import KsIndexLean.DiskAngularProjection
public import KsIndexLean.DiskTraceCovariance
public import KsIndexLean.WeakBoundaryDomains

@[expose] public section


noncomputable section
open Set MeasureTheory intervalIntegral
namespace KsIndex.Trace
open KsIndex.WeakH1

/-! ### `2π`-periodicity of the rotation action -/

lemma diskLpRotation_two_pi (f : L2C) : diskLpRotation (2 * Real.pi) f = f := by
  change Lp.compMeasurePreserving (planeRotation (2 * Real.pi)) _ f = f
  have h : (planeRotation (2 * Real.pi) : ℂ → ℂ) = id := by
    ext z
    simp [planeRotation_apply, Complex.exp_two_pi_mul_I]
  simp only [h, Lp.compMeasurePreserving_id_apply]

lemma diskRotation_two_pi (u : ComplexH1) : diskRotation (2 * Real.pi) u = u := by
  apply valueCLM_injective
  change valueCLM (diskH1Rotation (2 * Real.pi) u) = _
  rw [diskH1Rotation_value, diskLpRotation_two_pi]

lemma diskRotation_periodic (u : ComplexH1) :
    Function.Periodic (fun θ => diskRotation θ u) (2 * Real.pi) := by
  intro θ
  simp only
  rw [diskRotation_add, diskRotation_two_pi]

/-! ### The angular average -/

/-- The angular average `P₀ u`, the paper's projection onto the
`S¹`-invariants. -/
def angularAverage (u : ComplexH1) : ComplexH1 :=
  (2 * Real.pi)⁻¹ • ∫ θ in (0:ℝ)..(2 * Real.pi), diskRotation θ u

lemma intervalIntegrable_diskRotation (u : ComplexH1) (a b : ℝ) :
    IntervalIntegrable (fun θ => diskRotation θ u) volume a b :=
  (continuous_diskRotation u).intervalIntegrable a b

/-! ### Invariance, idempotence, range -/

/-- The average is invariant under every rotation. -/
lemma diskRotation_angularAverage (φ : ℝ) (u : ComplexH1) :
    diskRotation φ (angularAverage u) = angularAverage u := by
  unfold angularAverage
  change (diskRotation φ).toContinuousLinearMap
    ((2 * Real.pi)⁻¹ • ∫ θ in (0:ℝ)..(2 * Real.pi), diskRotation θ u) = _
  rw [ContinuousLinearMap.map_smul_of_tower]
  refine congrArg (fun t => (2 * Real.pi)⁻¹ • t) ?_
  rw [← ContinuousLinearMap.intervalIntegral_comp_comm _
    (intervalIntegrable_diskRotation u 0 (2 * Real.pi))]
  have hcongr : (fun θ => (diskRotation φ).toContinuousLinearMap (diskRotation θ u)) =
      fun θ => diskRotation (φ + θ) u := by
    funext θ
    exact (diskRotation_add φ θ u).symm
  rw [hcongr]
  calc ∫ θ in (0:ℝ)..(2 * Real.pi), diskRotation (φ + θ) u
      = ∫ θ in φ + 0..φ + 2 * Real.pi, diskRotation θ u :=
        integral_comp_add_left (fun θ => diskRotation θ u) φ
    _ = ∫ θ in (0:ℝ)..(2 * Real.pi), diskRotation θ u := by
        have h := (diskRotation_periodic u).intervalIntegral_add_eq (φ + 0) 0
        simpa using h

/-- The average of an invariant element is itself. -/
lemma angularAverage_of_invariant {u : ComplexH1}
    (h : ∀ θ, diskRotation θ u = u) : angularAverage u = u := by
  unfold angularAverage
  simp only [h]
  rw [intervalIntegral.integral_const, sub_zero, smul_smul,
    inv_mul_cancel₀ (ne_of_gt Real.two_pi_pos), one_smul]

lemma angularAverage_idem (u : ComplexH1) :
    angularAverage (angularAverage u) = angularAverage u :=
  angularAverage_of_invariant (fun θ => diskRotation_angularAverage θ u)

/-- Range characterization: the fixed points of `P₀` are exactly the full
`S¹`-invariants (the paper's `H¹_{S¹}(S²₋)`). -/
lemma angularAverage_eq_self_iff (u : ComplexH1) :
    angularAverage u = u ↔ ∀ θ, diskRotation θ u = u := by
  constructor
  · intro h θ
    calc diskRotation θ u = diskRotation θ (angularAverage u) := by rw [h]
      _ = angularAverage u := diskRotation_angularAverage θ u
      _ = u := h
  · exact angularAverage_of_invariant

/-! ### Linearity and the continuous-linear bundle -/

lemma angularAverage_add (u v : ComplexH1) :
    angularAverage (u + v) = angularAverage u + angularAverage v := by
  unfold angularAverage
  have h : (∫ θ in (0:ℝ)..(2 * Real.pi), diskRotation θ (u + v)) =
      (∫ θ in (0:ℝ)..(2 * Real.pi), diskRotation θ u) +
      ∫ θ in (0:ℝ)..(2 * Real.pi), diskRotation θ v := by
    rw [← integral_add (intervalIntegrable_diskRotation u 0 (2 * Real.pi))
      (intervalIntegrable_diskRotation v 0 (2 * Real.pi))]
    apply integral_congr
    intro θ _
    exact (diskRotation θ).map_add u v
  rw [h, smul_add]

lemma angularAverage_smul (c : ℂ) (u : ComplexH1) :
    angularAverage (c • u) = c • angularAverage u := by
  unfold angularAverage
  have h : (∫ θ in (0:ℝ)..(2 * Real.pi), diskRotation θ (c • u)) =
      c • ∫ θ in (0:ℝ)..(2 * Real.pi), diskRotation θ u := by
    rw [← intervalIntegral.integral_smul]
    apply integral_congr
    intro θ _
    exact (diskRotation θ).map_smul c u
  rw [h]
  exact (smul_comm c ((2 * Real.pi)⁻¹) _).symm

lemma norm_angularAverage_le (u : ComplexH1) : ‖angularAverage u‖ ≤ ‖u‖ := by
  unfold angularAverage
  rw [norm_smul]
  have hb : ‖∫ θ in (0:ℝ)..(2 * Real.pi), diskRotation θ u‖ ≤ ‖u‖ * |2 * Real.pi - 0| := by
    apply intervalIntegral.norm_integral_le_of_norm_le_const
    intro θ _
    exact le_of_eq ((diskRotation θ).norm_map u)
  have hpos : (0:ℝ) < 2 * Real.pi := Real.two_pi_pos
  calc ‖(2 * Real.pi)⁻¹‖ * ‖∫ θ in (0:ℝ)..(2 * Real.pi), diskRotation θ u‖
      ≤ (2 * Real.pi)⁻¹ * (‖u‖ * |2 * Real.pi - 0|) := by
        rw [Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hpos)]
        exact mul_le_mul_of_nonneg_left hb (inv_pos.mpr hpos).le
    _ = ‖u‖ := by
        rw [sub_zero, abs_of_pos hpos]
        field_simp

/-- `P₀` as a continuous linear map. -/
def angularAverageCLM : ComplexH1 →L[ℂ] ComplexH1 :=
  LinearMap.mkContinuous
    { toFun := angularAverage
      map_add' := angularAverage_add
      map_smul' := angularAverage_smul } 1
    (fun u => by simpa using norm_angularAverage_le u)

@[simp] lemma angularAverageCLM_apply (u : ComplexH1) :
    angularAverageCLM u = angularAverage u := rfl

/-! ### Character-class stability and the zero-mean domain -/

/-- `P₀` lands in every weak character class with eigenvalue one; in
particular it preserves the class-zero sector. -/
lemma angularAverage_mem_weakCharacterDomain (θ : ℝ) (u : ComplexH1) :
    angularAverage u ∈ weakCharacterDomain θ 1 := by
  rw [mem_weakCharacterDomain, one_smul]
  exact diskRotation_angularAverage θ u

/-- The zero-angular-mean pure-Neumann class-zero domain
(the paper's `H¹_{(0;k),⊥}` with Neumann boundary flags). -/
def zeroMeanDomain (k : ℕ) : Submodule ℂ ComplexH1 :=
  LinearMap.ker angularAverageCLM.toLinearMap ⊓ mixedCharacterDomain k 0 true true

lemma mem_zeroMeanDomain {k : ℕ} (u : ComplexH1) :
    u ∈ zeroMeanDomain k ↔
      angularAverage u = 0 ∧ u ∈ mixedCharacterDomain k 0 true true := by
  simp only [zeroMeanDomain, Submodule.mem_inf, LinearMap.mem_ker]
  rfl

lemma isClosed_zeroMeanDomain (k : ℕ) :
    IsClosed (zeroMeanDomain k : Set ComplexH1) := by
  rw [show (zeroMeanDomain k : Set ComplexH1) =
    (LinearMap.ker angularAverageCLM.toLinearMap : Set ComplexH1) ∩
      (mixedCharacterDomain k 0 true true : Set ComplexH1) from rfl]
  exact IsClosed.inter angularAverageCLM.isClosed_ker
    (isClosed_mixedCharacterDomain k 0 true true)

end KsIndex.Trace
