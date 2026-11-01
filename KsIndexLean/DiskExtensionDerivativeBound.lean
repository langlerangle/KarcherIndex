module

public import KsIndexLean.DiskReflectionExtension
public import KsIndexLean.OuterInversionBound
public import KsIndexLean.SphericalJoinedJet
public import KsIndexLean.InversionJetTransition
public import KsIndexLean.CollarInversionDerivative

@[expose] public section


noncomputable section
open Set MeasureTheory
namespace KsIndex.Trace
open KsIndex.WeakH1 KsIndex.Bracket

lemma diskExtensionJet_outer (u : ComplexH1) {z : ℂ}
    (hz : z ∈ annulusSet (1 : ℝ) 2) :
    diskExtensionJet u z = (Dxy (dxLp u) (dyLp u) (σ z)).comp (fderiv ℝ σ z) := by
  have hz0 : z ≠ 0 := norm_pos_iff.mp (by linarith [hz.1])
  have hs0 : σ z ≠ 0 := by simp [σ, hz0]
  have hs : ‖σ z‖ ≤ 1 := by
    rw [norm_σ]
    exact (inv_le_one₀ (by linarith [hz.1])).mpr hz.1.le
  have he := joinedDiskJet_reflection u u (c := 1) (by norm_num) hz0 (ne_of_gt hz.1)
  rw [KsIndex.Spherical.joinedDiskJet_eq_coordinates u u 1 hs0 hs] at he
  simpa only [diskExtensionJet, ite_eq_right (not_lt.mpr hz.1.le), inv_one, one_smul] using he.symm

lemma diskExtensionJet_outer_bound (u : ComplexH1) (d : ℂ) {z : ℂ}
    (hz : z ∈ annulusSet (1 : ℝ) 2) :
    ‖diskExtensionJet u z d‖ ≤
      (4 * ‖d‖) * (‖dxLp u (σ z)‖ + ‖dyLp u (σ z)‖) := by
  rw [diskExtensionJet_outer u hz, ContinuousLinearMap.comp_apply, Dxy_apply]
  have hb := sigma_collar_derivative_bound
    (show z ∈ annulusSet (1 / 2 : ℝ) 2 from ⟨by linarith [hz.1], hz.2⟩) d
  calc
    _ ≤ ‖(fderiv ℝ σ z d).re • dxLp u (σ z)‖ +
        ‖(fderiv ℝ σ z d).im • dyLp u (σ z)‖ := norm_add_le _ _
    _ ≤ (4 * ‖d‖) * ‖dxLp u (σ z)‖ + (4 * ‖d‖) * ‖dyLp u (σ z)‖ := by
      simp only [norm_smul, Real.norm_eq_abs]
      exact add_le_add
        (mul_le_mul_of_nonneg_right ((Complex.abs_re_le_norm _).trans hb) (norm_nonneg _))
        (mul_le_mul_of_nonneg_right ((Complex.abs_im_le_norm _).trans hb) (norm_nonneg _))
    _ = _ := by ring

end KsIndex.Trace
