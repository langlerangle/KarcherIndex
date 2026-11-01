module

public import KsIndexLean.KarcherLocalHarmonic
public import Mathlib.Analysis.Calculus.FDeriv.Symmetric

@[expose] public section


/-! Local Euclidean fundamental forms and scalar mean curvature.
The formulas are totalized at singular maps; their geometric interpretation is
used only with the proved immersion and unit-normal hypotheses. -/
noncomputable section
open scoped ContDiff
open InnerProductSpace
namespace KsIndex.KarcherData

abbrev AmbientTriple := ℝ × ℝ × ℝ

def euclideanDot (a b : AmbientTriple) : ℝ :=
  a.1 * b.1 + a.2.1 * b.2.1 + a.2.2 * b.2.2

def euclideanCross (a b : AmbientTriple) : AmbientTriple :=
  (a.2.1*b.2.2-a.2.2*b.2.1, a.2.2*b.1-a.1*b.2.2, a.1*b.2.1-a.2.1*b.1)

lemma euclideanCross_sq (a b : AmbientTriple) :
    euclideanSq (euclideanCross a b) = euclideanSq a * euclideanSq b - euclideanDot a b ^ 2 := by
  simp only [euclideanSq, euclideanDot, euclideanCross]
  ring

lemma euclideanCross_dot_left (a b : AmbientTriple) :
    euclideanDot (euclideanCross a b) a = 0 := by
  simp only [euclideanDot, euclideanCross]
  ring

lemma euclideanCross_dot_right (a b : AmbientTriple) :
    euclideanDot (euclideanCross a b) b = 0 := by
  simp only [euclideanDot, euclideanCross]
  ring

/-- The actual first fundamental form, pulled back by the real derivative. -/
def firstFundamentalForm (X : ℂ → AmbientTriple) (w u v : ℂ) : ℝ :=
  euclideanDot (fderiv ℝ X w u) (fderiv ℝ X w v)

/-- Positive-coordinate orientation: normalize X_u cross X_v with the Euclidean length. -/
def chartUnitNormal (X : ℂ → AmbientTriple) (w : ℂ) : AmbientTriple :=
  (Real.sqrt (euclideanSq (euclideanCross (fderiv ℝ X w 1) (fderiv ℝ X w Complex.I))))⁻¹ •
    euclideanCross (fderiv ℝ X w 1) (fderiv ℝ X w Complex.I)

/-- Normal component of the actual coordinate Hessian: a bilinear form, not an
assumed curvature coefficient. -/
def secondFundamentalForm (X : ℂ → AmbientTriple) (w : ℂ) : ℂ →ₗ[ℝ] ℂ →ₗ[ℝ] ℝ :=
  (chartUnitNormal X w).1 • bilinearIteratedFDerivTwo ℝ (fun z => (X z).1) w +
  (chartUnitNormal X w).2.1 • bilinearIteratedFDerivTwo ℝ (fun z => (X z).2.1) w +
  (chartUnitNormal X w).2.2 • bilinearIteratedFDerivTwo ℝ (fun z => (X z).2.2) w

/-- Scalar mean curvature H = one half of the metric trace of II. The orientation
is that of chartUnitNormal; reversing it reverses H but preserves H = 0. -/
def chartMeanCurvature (X : ℂ → AmbientTriple) (w : ℂ) : ℝ :=
  (firstFundamentalForm X w Complex.I Complex.I * secondFundamentalForm X w 1 1 -
    2 * firstFundamentalForm X w 1 Complex.I * secondFundamentalForm X w 1 Complex.I +
    firstFundamentalForm X w 1 1 * secondFundamentalForm X w Complex.I Complex.I) /
  (2 * (firstFundamentalForm X w 1 1 * firstFundamentalForm X w Complex.I Complex.I -
    firstFundamentalForm X w 1 Complex.I ^ 2))

lemma metric_coefficients_of_conformal {D : ℂ →L[ℝ] AmbientTriple} {q : ℝ}
    (h : ∀ d : ℂ, euclideanSq (D d) = q * ‖d‖ ^ 2) :
    euclideanDot (D 1) (D 1) = q ∧ euclideanDot (D 1) (D Complex.I) = 0 ∧
    euclideanDot (D Complex.I) (D Complex.I) = q := by
  have h1 := h 1
  have hi := h Complex.I
  have ha := h (1 + Complex.I)
  simp only [norm_one, Complex.norm_I, one_pow, mul_one] at h1 hi
  have hn : ‖(1 : ℂ) + Complex.I‖ ^ 2 = 2 := by
    rw [Complex.sq_norm]
    norm_num [Complex.normSq_apply]
  rw [hn, map_add] at ha
  simp only [euclideanSq, Prod.fst_add, Prod.snd_add] at h1 hi ha
  simp only [euclideanDot]
  constructor
  · nlinarith [h1]
  constructor
  · nlinarith [ha, h1, hi]
  · nlinarith [hi]

lemma euclideanSq_smul (c : ℝ) (a : AmbientTriple) :
    euclideanSq (c • a) = c ^ 2 * euclideanSq a := by
  simp only [euclideanSq, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
  ring

lemma euclideanDot_smul_left (c : ℝ) (a b : AmbientTriple) :
    euclideanDot (c • a) b = c * euclideanDot a b := by
  simp only [euclideanDot, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
  ring

/-- At a positive conformal metric the cross-product normal is genuinely unit
and perpendicular to both coordinate tangents. -/
theorem chartUnitNormal_spec {X : ℂ → AmbientTriple} {w : ℂ} {q : ℝ}
    (hq : 0 < q)
    (hm : ∀ d : ℂ, euclideanSq (fderiv ℝ X w d) = q * ‖d‖ ^ 2) :
    euclideanSq (chartUnitNormal X w) = 1 ∧
    euclideanDot (chartUnitNormal X w) (fderiv ℝ X w 1) = 0 ∧
    euclideanDot (chartUnitNormal X w) (fderiv ℝ X w Complex.I) = 0 := by
  obtain ⟨hE, hF, hG⟩ := metric_coefficients_of_conformal hm
  have h1 : euclideanSq (fderiv ℝ X w 1) = q := by simpa using hm 1
  have hi : euclideanSq (fderiv ℝ X w Complex.I) = q := by simpa using hm Complex.I
  have hc : euclideanSq (euclideanCross (fderiv ℝ X w 1) (fderiv ℝ X w Complex.I)) = q ^ 2 := by
    rw [euclideanCross_sq, h1, hi, hF]
    ring
  have hn : chartUnitNormal X w = q⁻¹ •
      euclideanCross (fderiv ℝ X w 1) (fderiv ℝ X w Complex.I) := by
    unfold chartUnitNormal
    rw [hc, Real.sqrt_sq hq.le]
  rw [hn]
  refine ⟨?_, ?_, ?_⟩
  · rw [euclideanSq_smul, hc, inv_pow, inv_mul_cancel₀ (pow_ne_zero 2 hq.ne')]
  · rw [euclideanDot_smul_left, euclideanCross_dot_left, mul_zero]
  · rw [euclideanDot_smul_left, euclideanCross_dot_right, mul_zero]

/-- C² coordinate functions make the actual Hessian-normal form symmetric. -/
lemma secondFundamentalForm_symmetric {X : ℂ → AmbientTriple} {U : Set ℂ}
    (h : HarmonicCoordinates X U) {w : ℂ} (hw : w ∈ U) (u v : ℂ) :
    secondFundamentalForm X w u v = secondFundamentalForm X w v u := by
  have h1 := (h.1 w hw).1.isSymmSndFDerivAt (by simp)
  have h2 := (h.2.1 w hw).1.isSymmSndFDerivAt (by simp)
  have h3 := (h.2.2 w hw).1.isSymmSndFDerivAt (by simp)
  have hb (f : ℂ → ℝ) (hf : IsSymmSndFDerivAt ℝ f w) :
      bilinearIteratedFDerivTwo ℝ f w u v = bilinearIteratedFDerivTwo ℝ f w v u := by
    exact hf u v
  simp only [secondFundamentalForm, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul]
  rw [hb _ h1, hb _ h2, hb _ h3]

lemma harmonic_hessian_trace {f : ℂ → ℝ} {w : ℂ} (h : HarmonicAt f w) :
    bilinearIteratedFDerivTwo ℝ f w 1 1 +
      bilinearIteratedFDerivTwo ℝ f w Complex.I Complex.I = 0 := by
  have he := h.2.eq_of_nhds
  simpa only [laplacian_eq_iteratedFDeriv_complexPlane,
    bilinearIteratedFDerivTwo_eq_iteratedFDeriv, Pi.zero_apply] using he

lemma secondFundamentalForm_trace_zero {X : ℂ → AmbientTriple} {U : Set ℂ}
    (h : HarmonicCoordinates X U) {w : ℂ} (hw : w ∈ U) :
    secondFundamentalForm X w 1 1 + secondFundamentalForm X w Complex.I Complex.I = 0 := by
  have h1 := harmonic_hessian_trace (h.1 w hw)
  have h2 := harmonic_hessian_trace (h.2.1 w hw)
  have h3 := harmonic_hessian_trace (h.2.2 w hw)
  simp only [secondFundamentalForm, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul]
  linear_combination (chartUnitNormal X w).1 * h1 +
    (chartUnitNormal X w).2.1 * h2 + (chartUnitNormal X w).2.2 * h3

/-- Harmonic coordinates with a conformal induced metric have zero scalar mean curvature. -/
theorem chartMeanCurvature_eq_zero {X : ℂ → AmbientTriple} {U : Set ℂ}
    (h : HarmonicCoordinates X U) {w : ℂ} (hw : w ∈ U) {q : ℝ}
    (hm : ∀ d : ℂ, euclideanSq (fderiv ℝ X w d) = q * ‖d‖ ^ 2) :
    chartMeanCurvature X w = 0 := by
  obtain ⟨hE, hF, hG⟩ := metric_coefficients_of_conformal hm
  have ht := secondFundamentalForm_trace_zero h hw
  unfold chartMeanCurvature firstFundamentalForm
  rw [hE, hF, hG]
  have hn : q * secondFundamentalForm X w 1 1 - 2 * 0 * secondFundamentalForm X w 1 Complex.I +
      q * secondFundamentalForm X w Complex.I Complex.I = 0 := by
    linear_combination q * ht
  rw [hn, zero_div]

/-- In conformal coordinates the metric determinant is positive, so the
inverse-metric trace formula is nonsingular. -/
lemma firstFundamentalForm_determinant_pos {X : ℂ → AmbientTriple} {w : ℂ} {q : ℝ}
    (hq : 0 < q)
    (hm : ∀ d : ℂ, euclideanSq (fderiv ℝ X w d) = q * ‖d‖ ^ 2) :
    0 < firstFundamentalForm X w 1 1 * firstFundamentalForm X w Complex.I Complex.I -
      firstFundamentalForm X w 1 Complex.I ^ 2 := by
  obtain ⟨hE, hF, hG⟩ := metric_coefficients_of_conformal hm
  unfold firstFundamentalForm
  rw [hE, hF, hG]
  nlinarith

/-- The scalar mean curvature is the half-trace of the Hessian-normal form
with respect to the actual positive conformal first fundamental form. -/
lemma chartMeanCurvature_conformal {X : ℂ → AmbientTriple} {w : ℂ} {q : ℝ}
    (hq : 0 < q)
    (hm : ∀ d : ℂ, euclideanSq (fderiv ℝ X w d) = q * ‖d‖ ^ 2) :
    chartMeanCurvature X w =
      (secondFundamentalForm X w 1 1 + secondFundamentalForm X w Complex.I Complex.I) / (2 * q) := by
  obtain ⟨hE, hF, hG⟩ := metric_coefficients_of_conformal hm
  unfold chartMeanCurvature firstFundamentalForm
  rw [hE, hF, hG]
  have hne := hq.ne'
  field_simp
  ring

lemma rho_sq_pos {k : ℕ} (hk : 2 ≤ k) {w : ℂ} (hw : w ∉ Surface.punctures k) :
    0 < Surface.rho k w ^ 2 := by
  have hp := ewRealDifferential_metric_pos hk hw (show (1 : ℂ) ≠ 0 by simp)
  simpa [ewRealDifferential_metric hk] using hp

/-- EW finite-chart representatives have a genuine Euclidean unit normal. -/
lemma ew_chartUnitNormal_spec {k : ℕ} (hk : 2 ≤ k) {X : ℂ → AmbientTriple} {w : ℂ}
    (hw : w ∉ Surface.punctures k) (hd : HasFDerivAt X (ewRealDifferential k w) w) :
    euclideanSq (chartUnitNormal X w) = 1 ∧
    euclideanDot (chartUnitNormal X w) (fderiv ℝ X w 1) = 0 ∧
    euclideanDot (chartUnitNormal X w) (fderiv ℝ X w Complex.I) = 0 := by
  apply chartUnitNormal_spec (rho_sq_pos hk hw)
  intro d
  rw [hd.fderiv, ewRealDifferential_metric hk]

/-- The corresponding assertion in the infinity chart, including its center. -/
lemma infinity_chartUnitNormal_spec {k : ℕ} (hk : 2 ≤ k) {X : ℂ → AmbientTriple} {v : ℂ}
    (hv : v ∉ Surface.punctures k) (hd : HasFDerivAt X (infinityRealDifferential k v) v) :
    euclideanSq (chartUnitNormal X v) = 1 ∧
    euclideanDot (chartUnitNormal X v) (fderiv ℝ X v 1) = 0 ∧
    euclideanDot (chartUnitNormal X v) (fderiv ℝ X v Complex.I) = 0 := by
  apply chartUnitNormal_spec (rho_sq_pos hk hv)
  intro d
  rw [hd.fderiv, infinityRealDifferential_metric hk]

/-- Actual finite-chart representatives have zero mean curvature, with the
first and second fundamental forms taken from their real derivatives. -/
theorem exists_zero_mean_curvature_local_representative {k : ℕ} (hk : 2 ≤ k)
    (b x : PuncturedPlane k) :
    ∃ r : ℝ, 0 < r ∧ ∃ X : ℂ → AmbientTriple,
      X x.val = 0 ∧ ContDiffOn ℝ ∞ X (Metric.ball x.val r) ∧
      HarmonicCoordinates X (Metric.ball x.val r) ∧
      (∀ w ∈ Metric.ball x.val r, HasFDerivAt X (ewRealDifferential k w) w) ∧
      (∀ y : PuncturedPlane k, y.val ∈ Metric.ball x.val r →
        descendedIntegral hk b y = descendedIntegral hk b x + projectPeriod (X y.val)) ∧
      (∀ w ∈ Metric.ball x.val r, chartMeanCurvature X w = 0) := by
  obtain ⟨r, hr, X, hz, hs, hh, hd, he, _⟩ :=
    exists_smooth_harmonic_local_representative hk b x
  refine ⟨r, hr, X, hz, hs, hh, hd, he, ?_⟩
  intro w hw
  apply chartMeanCurvature_eq_zero hh hw
  intro d
  rw [(hd w hw).fderiv, ewRealDifferential_metric hk]

/-- Zero mean curvature also holds across the regular infinity point, with
exact overlap identification and a genuine unit normal throughout the disk. -/
theorem exists_zero_mean_curvature_infinity_chart {k : ℕ} (hk : 2 ≤ k)
    (b : PuncturedPlane k) :
    ∃ r : ℝ, ∃ _hr0 : 0 < r, ∃ hr1 : r < 1,
    ∃ X : ℂ → AmbientTriple, ∃ C : PeriodTarget,
      X 0 = 0 ∧ ContDiffOn ℝ ∞ X (Metric.ball (0 : ℂ) r) ∧
      HarmonicCoordinates X (Metric.ball (0 : ℂ) r) ∧
      (∀ v ∈ Metric.ball (0 : ℂ) r, HasFDerivAt X (infinityRealDifferential k v) v) ∧
      (∀ v ∈ Metric.ball (0 : ℂ) r, Function.Injective (infinityRealDifferential k v)) ∧
      (∀ v : infinityOverlap r,
        descendedIntegral hk b (infinityOverlapPoint hk hr1.le v) = C + projectPeriod (X v.val)) ∧
      (∀ v ∈ Metric.ball (0 : ℂ) r, euclideanSq (chartUnitNormal X v) = 1 ∧
        chartMeanCurvature X v = 0) := by
  obtain ⟨r, hr0, hr1, X, C, hz, hs, hh, hd, hi, he⟩ :=
    exists_smooth_harmonic_infinity_chart hk b
  refine ⟨r, hr0, hr1, X, C, hz, hs, hh, hd, hi, he, ?_⟩
  intro v hv
  have hp : v ∉ Surface.punctures k :=
    not_puncture_of_norm_lt_one hk ((by simpa using hv : ‖v‖ < r).trans hr1)
  refine ⟨(infinity_chartUnitNormal_spec hk hp (hd v hv)).1, ?_⟩
  apply chartMeanCurvature_eq_zero hh hv
  intro d
  rw [(hd v hv).fderiv, infinityRealDifferential_metric hk]

end KsIndex.KarcherData
