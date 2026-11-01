module

public import KsIndexLean.RawCartesianIdentity

@[expose] public section


open Set MeasureTheory
open scoped ContDiff InnerProductSpace

noncomputable section
namespace KsIndex.Trace

lemma memLp_bdd_real_smul {μ : Measure ℂ} {u : ℂ → ℂ} {S : ℂ → ℝ} {C : ℝ}
    (hS : AEStronglyMeasurable S μ) (hC : ∀ᵐ z ∂μ, |S z| ≤ C) (hu : MemLp u 2 μ) :
    MemLp (fun z => S z • u z) 2 μ := by
  rw [memLp_iff]
  refine lt_of_le_of_lt (eLpNorm_mono_ae (hS.smul hu.aestronglyMeasurable) ?_)
    (hu.const_smul C).eLpNorm_lt_top
  filter_upwards [hC] with z hz
  simp only [Pi.smul_apply, norm_smul, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_right (hz.trans (le_abs_self C)) (norm_nonneg _)

def polarCoefficient (L : ℂ →L[ℝ] ℝ) (n : ℕ) (z : ℂ) : ℝ := L z / ‖z‖ ^ n

lemma continuousOn_polarCoefficient {a b : ℝ} (ha : 0 < a) (L : ℂ →L[ℝ] ℝ) (n : ℕ) :
    ContinuousOn (polarCoefficient L n) (annulusSet a b) :=
  L.continuous.continuousOn.div (continuous_norm.pow n).continuousOn
    (fun _ hz => pow_ne_zero n (ne_of_gt (ha.trans hz.1)))

lemma polarCoefficient_one_bound {a b : ℝ} (ha : 0 < a) (L : ℂ →L[ℝ] ℝ)
    (hL : ∀ z, |L z| ≤ ‖z‖) {z : ℂ} (hz : z ∈ annulusSet a b) :
    |polarCoefficient L 1 z| ≤ 1 := by
  have hn := ha.trans hz.1
  simp only [polarCoefficient, pow_one, abs_div, abs_of_pos hn]
  exact (div_le_one hn).mpr (hL z)

lemma polarCoefficient_two_bound {a b : ℝ} (ha : 0 < a) (L : ℂ →L[ℝ] ℝ)
    (hL : ∀ z, |L z| ≤ ‖z‖) {z : ℂ} (hz : z ∈ annulusSet a b) :
    |polarCoefficient L 2 z| ≤ 1 / a := by
  have hn := ha.trans hz.1
  simp only [polarCoefficient, abs_div, abs_pow, abs_norm]
  calc
    |L z| / ‖z‖ ^ 2 ≤ ‖z‖ / ‖z‖ ^ 2 :=
      div_le_div_of_nonneg_right (hL z) (sq_nonneg _)
    _ = 1 / ‖z‖ := by field_simp
    _ ≤ 1 / a := one_div_le_one_div_of_le ha hz.1.le

lemma memLp_polarCoefficient_one {a b : ℝ} (ha : 0 < a) (L : ℂ →L[ℝ] ℝ)
    (hL : ∀ z, |L z| ≤ ‖z‖) {u : ℂ → ℂ}
    (hu : MemLp u 2 (volume.restrict (annulusSet a b))) :
    MemLp (fun z => polarCoefficient L 1 z • u z) 2 (volume.restrict (annulusSet a b)) := by
  apply memLp_bdd_real_smul (C := 1)
    ((continuousOn_polarCoefficient ha L 1).aestronglyMeasurable measurableSet_annulusSet) _ hu
  filter_upwards [ae_restrict_mem measurableSet_annulusSet] with z hz
  exact polarCoefficient_one_bound ha L hL hz

lemma memLp_polarCoefficient_two {a b : ℝ} (ha : 0 < a) (L : ℂ →L[ℝ] ℝ)
    (hL : ∀ z, |L z| ≤ ‖z‖) {u : ℂ → ℂ}
    (hu : MemLp u 2 (volume.restrict (annulusSet a b))) :
    MemLp (fun z => polarCoefficient L 2 z • u z) 2 (volume.restrict (annulusSet a b)) := by
  apply memLp_bdd_real_smul (C := 1 / a)
    ((continuousOn_polarCoefficient ha L 2).aestronglyMeasurable measurableSet_annulusSet) _ hu
  filter_upwards [ae_restrict_mem measurableSet_annulusSet] with z hz
  exact polarCoefficient_two_bound ha L hL hz

def reconstructedX (v q : ℂ → ℂ) (z : ℂ) : ℂ :=
  polarCoefficient Complex.reCLM 1 z • v z - polarCoefficient Complex.imCLM 2 z • q z

def reconstructedY (v q : ℂ → ℂ) (z : ℂ) : ℂ :=
  polarCoefficient Complex.imCLM 1 z • v z + polarCoefficient Complex.reCLM 2 z • q z

lemma memLp_reconstructedX {a b : ℝ} (ha : 0 < a) {v q : ℂ → ℂ}
    (hv : MemLp v 2 (volume.restrict (annulusSet a b)))
    (hq : MemLp q 2 (volume.restrict (annulusSet a b))) :
    MemLp (reconstructedX v q) 2 (volume.restrict (annulusSet a b)) :=
  (memLp_polarCoefficient_one ha Complex.reCLM Complex.abs_re_le_norm hv).sub
    (memLp_polarCoefficient_two ha Complex.imCLM Complex.abs_im_le_norm hq)

lemma memLp_reconstructedY {a b : ℝ} (ha : 0 < a) {v q : ℂ → ℂ}
    (hv : MemLp v 2 (volume.restrict (annulusSet a b)))
    (hq : MemLp q 2 (volume.restrict (annulusSet a b))) :
    MemLp (reconstructedY v q) 2 (volume.restrict (annulusSet a b)) :=
  (memLp_polarCoefficient_one ha Complex.imCLM Complex.abs_im_le_norm hv).add
    (memLp_polarCoefficient_two ha Complex.reCLM Complex.abs_re_le_norm hq)

end KsIndex.Trace
