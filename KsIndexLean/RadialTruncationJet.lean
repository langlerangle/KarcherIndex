module

public import KsIndexLean.RadialTruncation
public import Mathlib.Analysis.Calculus.Deriv.Inv

@[expose] public section


open Set MeasureTheory Filter Topology
open scoped ContDiff
noncomputable section
namespace KsIndex.Trace

def radialWeightJet (t : ℝ) (z : ℂ) : ℂ →L[ℝ] ℝ :=
  (-(t / Real.sqrt (1 + t * ‖z‖ ^ 2) ^ 3)) • innerSL ℝ z

def radialJet (t : ℝ) (z : ℂ) : ℂ →L[ℝ] ℂ :=
  radialWeight t z • ContinuousLinearMap.id ℝ ℂ + (radialWeightJet t z).smulRight z

lemma radialWeight_hasFDerivAt {t : ℝ} (ht : 0 ≤ t) (z : ℂ) :
    HasFDerivAt (radialWeight t) (radialWeightJet t z) z := by
  have hn := ((hasStrictFDerivAt_norm_sq z).hasFDerivAt.const_mul t).const_add 1
  have hs := hn.sqrt (radial_den_pos ht z).ne'
  have hs0 : Real.sqrt (1 + t * ‖z‖ ^ 2) ≠ 0 :=
    (Real.sqrt_pos.mpr (radial_den_pos ht z)).ne'
  have hi := (hasDerivAt_inv hs0).comp_hasFDerivAt z hs
  apply hi.congr_fderiv
  ext w
  simp only [radialWeightJet, smul_apply, smul_eq_mul]
  field_simp
  ring

lemma radialTruncate_hasFDerivAt {t : ℝ} (ht : 0 ≤ t) (z : ℂ) :
    HasFDerivAt (radialTruncate t) (radialJet t z) z :=
  (radialWeight_hasFDerivAt ht z).smul (hasFDerivAt_id z)

lemma radialJet_continuous {t : ℝ} (ht : 0 ≤ t) : Continuous (radialJet t) := by
  have he : radialJet t = fderiv ℝ (radialTruncate t) := by
    funext z
    exact (radialTruncate_hasFDerivAt ht z).fderiv.symm
  rw [he]
  exact (radialTruncate_smooth ht).continuous_fderiv (by norm_num)

lemma radial_rank_norm_le {t : ℝ} (ht : 0 ≤ t) (z : ℂ) :
    ‖(radialWeightJet t z).smulRight z‖ ≤ 1 := by
  let s := Real.sqrt (1 + t * ‖z‖ ^ 2)
  have hs : 0 < s := Real.sqrt_pos.mpr (radial_den_pos ht z)
  have hs1 : 1 ≤ s := by
    apply Real.le_sqrt_of_sq_le
    nlinarith [mul_nonneg ht (sq_nonneg ‖z‖)]
  have hsq : s ^ 2 = 1 + t * ‖z‖ ^ 2 := Real.sq_sqrt (radial_den_pos ht z).le
  have he : ‖(radialWeightJet t z).smulRight z‖ = t * ‖z‖ ^ 2 / s ^ 3 := by
    rw [ContinuousLinearMap.norm_smulRight_apply, radialWeightJet, norm_smul,
      Real.norm_eq_abs, abs_neg, abs_of_nonneg (div_nonneg ht (pow_nonneg hs.le _)),
      innerSL_apply_norm]
    dsimp only [s]
    ring
  rw [he]
  apply (div_le_one (pow_pos hs 3)).mpr
  nlinarith [mul_nonneg (sq_nonneg s) (sub_nonneg.mpr hs1)]

lemma radialJet_norm_le {t : ℝ} (ht : 0 ≤ t) (z : ℂ) : ‖radialJet t z‖ ≤ 2 := by
  have h1 : ‖radialWeight t z • ContinuousLinearMap.id ℝ ℂ‖ ≤ 1 := by
    rw [norm_smul, ContinuousLinearMap.norm_id, mul_one, Real.norm_eq_abs,
      abs_of_nonneg (radialWeight_bounds ht z).1]
    exact (radialWeight_bounds ht z).2
  exact (norm_add_le _ _).trans (by linarith [radial_rank_norm_le ht z])

lemma radialTruncate_lipschitz {t : ℝ} (ht : 0 ≤ t) :
    LipschitzWith 2 (radialTruncate t) := by
  apply lipschitzWith_of_nnnorm_fderiv_le (𝕜 := ℝ)
    ((radialTruncate_smooth ht).differentiable (by simp))
  intro z
  rw [(radialTruncate_hasFDerivAt ht z).fderiv]
  exact_mod_cast radialJet_norm_le ht z

end KsIndex.Trace
