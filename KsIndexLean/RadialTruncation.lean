module

public import KsIndexLean.WeakH1ChainRule
public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Analysis.Calculus.MeanValue

@[expose] public section


open Set MeasureTheory Filter Topology
open scoped ContDiff
noncomputable section
namespace KsIndex.Trace

def radialWeight (t : ℝ) (z : ℂ) : ℝ := (Real.sqrt (1 + t * ‖z‖ ^ 2))⁻¹

def radialTruncate (t : ℝ) (z : ℂ) : ℂ := radialWeight t z • z

lemma radial_den_pos {t : ℝ} (ht : 0 ≤ t) (z : ℂ) : 0 < 1 + t * ‖z‖ ^ 2 :=
  add_pos_of_pos_of_nonneg zero_lt_one (mul_nonneg ht (sq_nonneg _))

lemma radialWeight_bounds {t : ℝ} (ht : 0 ≤ t) (z : ℂ) :
    0 ≤ radialWeight t z ∧ radialWeight t z ≤ 1 := by
  have hs : 1 ≤ Real.sqrt (1 + t * ‖z‖ ^ 2) := by
    rw [Real.le_sqrt (by norm_num) (radial_den_pos ht z).le]
    nlinarith [mul_nonneg ht (sq_nonneg ‖z‖)]
  exact ⟨inv_nonneg.mpr (Real.sqrt_nonneg _), inv_le_one_of_one_le₀ hs⟩

lemma radialTruncate_zero (t : ℝ) : radialTruncate t 0 = 0 := by
  simp [radialTruncate]

lemma radialTruncate_norm_le {t : ℝ} (ht : 0 ≤ t) (z : ℂ) :
    ‖radialTruncate t z‖ ≤ ‖z‖ := by
  rw [radialTruncate, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (radialWeight_bounds ht z).1]
  exact mul_le_of_le_one_left (norm_nonneg _) (radialWeight_bounds ht z).2

lemma radialTruncate_bounded {t : ℝ} (ht : 0 < t) (z : ℂ) :
    ‖radialTruncate t z‖ ≤ (Real.sqrt t)⁻¹ := by
  have hst : 0 < Real.sqrt t := Real.sqrt_pos.mpr ht
  have hs : 0 < Real.sqrt (1 + t * ‖z‖ ^ 2) := Real.sqrt_pos.mpr (radial_den_pos ht.le z)
  have hmul : Real.sqrt t * ‖z‖ ≤ Real.sqrt (1 + t * ‖z‖ ^ 2) := by
    have h1 := Real.sq_sqrt ht.le
    have h2 := Real.sq_sqrt (radial_den_pos ht.le z).le
    nlinarith [Real.sqrt_nonneg (1 + t * ‖z‖ ^ 2), norm_nonneg z]
  rw [radialTruncate, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (radialWeight_bounds ht.le z).1, radialWeight, inv_mul_eq_div,
    inv_eq_one_div]
  exact (div_le_div_iff₀ hs hst).mpr (by nlinarith)

lemma radialTruncate_phase (t : ℝ) (c z : ℂ) (hc : ‖c‖ = 1) :
    radialTruncate t (c * z) = c * radialTruncate t z := by
  simp only [radialTruncate, radialWeight, norm_mul, hc, one_mul, Complex.real_smul]
  ring

lemma radialWeight_smooth {t : ℝ} (ht : 0 ≤ t) : ContDiff ℝ ∞ (radialWeight t) := by
  have h : ContDiff ℝ ∞ (fun z : ℂ => 1 + t * ‖z‖ ^ 2) :=
    contDiff_const.add (contDiff_const.mul (contDiff_id.norm_sq ℝ))
  exact (h.sqrt (fun z => (radial_den_pos ht z).ne')).inv
    (fun z => (Real.sqrt_pos.mpr (radial_den_pos ht z)).ne')

lemma radialTruncate_smooth {t : ℝ} (ht : 0 ≤ t) : ContDiff ℝ ∞ (radialTruncate t) :=
  (radialWeight_smooth ht).smul contDiff_id

end KsIndex.Trace
