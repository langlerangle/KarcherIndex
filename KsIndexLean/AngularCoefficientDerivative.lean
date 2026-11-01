module

public import KsIndexLean.ReconstructedJetFrame
public import KsIndexLean.SupportedWeakProduct

@[expose] public section


open Set MeasureTheory
open scoped ContDiff

noncomputable section
namespace KsIndex.Trace

lemma angularCoefficient_contDiffOn {a b : ℝ} (ha : 0 < a) {η : ℂ → ℝ}
    (hη : ContDiff ℝ (⊤ : ℕ∞) η) :
    ContDiffOn ℝ (⊤ : ℕ∞) (fun z => η (nUnit z)) (annulusSet a b) := by
  intro z hz
  have hn : z ≠ 0 := norm_pos_iff.mp (ha.trans hz.1)
  have hu : ContDiffAt ℝ (⊤ : ℕ∞) nUnit z :=
    ((contDiffAt_norm ℝ hn).inv (norm_ne_zero_iff.mpr hn)).smul contDiffAt_id
  exact (hη.contDiffAt.comp z hu).contDiffWithinAt

lemma angularCoefficient_radial {η : ℂ → ℝ} (hη : ContDiff ℝ (⊤ : ℕ∞) η)
    {z : ℂ} (hz : z ≠ 0) : fderiv ℝ (fun w => η (nUnit w)) z z = 0 := by
  change fderiv ℝ (η ∘ nUnit) z z = 0
  rw [fderiv_comp z (hη.differentiable (by simp) _) (hasFDerivAt_nUnit hz).differentiableAt,
    ContinuousLinearMap.comp_apply, (hasFDerivAt_nUnit hz).fderiv,
    fderiv_nUnit_radial hz, map_zero]

lemma angularCoefficient_rotation {η : ℂ → ℝ} (hη : ContDiff ℝ (⊤ : ℕ∞) η)
    {z : ℂ} (hz : z ≠ 0) :
    fderiv ℝ (fun w => η (nUnit w)) z (z * Complex.I) = angularTestDeriv η (nUnit z) := by
  change fderiv ℝ (η ∘ nUnit) z (z * Complex.I) = _
  rw [fderiv_comp z (hη.differentiable (by simp) _) (hasFDerivAt_nUnit hz).differentiableAt,
    ContinuousLinearMap.comp_apply, fderiv_nUnit_rotation hz]
  rfl

end KsIndex.Trace
