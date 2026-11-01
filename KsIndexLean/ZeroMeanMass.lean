module

/-
KsIndexLean — ZeroMeanMass: the source-carrier identification ([ksindexi]
tex 1810–1838).  The paper defines `H¹_{(0;k),⊥}` as the `L²(S²₋)`-orthogonal
complement of the `S¹`-invariants inside the class-zero sector; the Lean
carrier is `ker P₀`.  This file proves they coincide: zero angular average is
exactly spherical-mass orthogonality to every rotation-invariant element —
so `zeroMeanDomain` is the paper's complement, not a bare `H¹`-projection
kernel.
-/
public import KsIndexLean.ZeroMeanProjection
public import KsIndexLean.WeakEigenTraceFourierSupport

@[expose] public section


noncomputable section
open Set MeasureTheory
namespace KsIndex.Trace
open KsIndex.WeakH1 KsIndex.Spherical

/-- Against an invariant element, the spherical mass pairing does not see
the angular average. -/
lemma mass_angularAverage_right (w u : ComplexH1)
    (hw : ∀ θ : ℝ, diskRotation θ w = w) :
    inner ℂ (weightedDiskValueCLM w) (weightedDiskValueCLM (angularAverage u)) =
      inner ℂ (weightedDiskValueCLM w) (weightedDiskValueCLM u) := by
  have hM : ∀ θ : ℝ,
      inner ℂ (weightedDiskValueCLM w) (weightedDiskValueCLM (diskRotation θ u)) =
        inner ℂ (weightedDiskValueCLM w) (weightedDiskValueCLM u) := by
    intro θ
    conv_lhs => rw [← hw θ]
    exact weightedDisk_mass_diskRotation θ w u
  change ((innerSL ℂ (weightedDiskValueCLM w)).comp weightedDiskValueCLM)
    (angularAverage u) = _
  unfold angularAverage
  rw [ContinuousLinearMap.map_smul_of_tower,
    ← ContinuousLinearMap.intervalIntegral_comp_comm _
      (intervalIntegrable_diskRotation u 0 (2 * Real.pi))]
  have hcongr : (fun θ =>
      ((innerSL ℂ (weightedDiskValueCLM w)).comp weightedDiskValueCLM)
        (diskRotation θ u)) =
      fun _ : ℝ => inner ℂ (weightedDiskValueCLM w) (weightedDiskValueCLM u) := by
    funext θ
    exact hM θ
  rw [hcongr, intervalIntegral.integral_const, sub_zero, smul_smul,
    inv_mul_cancel₀ (ne_of_gt Real.two_pi_pos), one_smul]

/-- **The carrier identification ([ksindexi] tex 1810–1838)**: zero angular
average is exactly `L²(S²₋)`-orthogonality to every `S¹`-invariant
element. -/
theorem angularAverage_eq_zero_iff_mass_orthogonal (u : ComplexH1) :
    angularAverage u = 0 ↔
      ∀ v : ComplexH1, (∀ θ : ℝ, diskRotation θ v = v) →
        inner ℂ (weightedDiskValueCLM v) (weightedDiskValueCLM u) = 0 := by
  constructor
  · intro hu v hv
    rw [← mass_angularAverage_right v u hv, hu, map_zero, inner_zero_right]
  · intro h
    have h0 := h (angularAverage u) (fun θ => diskRotation_angularAverage θ u)
    rw [← mass_angularAverage_right (angularAverage u) u
      (fun θ => diskRotation_angularAverage θ u)] at h0
    have hz : weightedDiskValueCLM (angularAverage u) = 0 :=
      inner_self_eq_zero.mp h0
    apply weightedDiskValueCLM_injective
    rw [hz, map_zero]

/-- The zero-mean domain is the paper's carrier: the mass-orthogonal
complement of the `S¹`-invariants inside the pure-Neumann class-zero
sector. -/
theorem mem_zeroMeanDomain_iff_mass_orthogonal {k : ℕ} (u : ComplexH1) :
    u ∈ zeroMeanDomain k ↔
      (∀ v : ComplexH1, (∀ θ : ℝ, diskRotation θ v = v) →
        inner ℂ (weightedDiskValueCLM v) (weightedDiskValueCLM u) = 0) ∧
      u ∈ mixedCharacterDomain k 0 true true := by
  rw [mem_zeroMeanDomain, angularAverage_eq_zero_iff_mass_orthogonal]

end KsIndex.Trace
