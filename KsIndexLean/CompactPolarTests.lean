module

public import KsIndexLean.FourierEigenTests
public import KsIndexLean.JacobiWeakTrace

@[expose] public section


noncomputable section
open Set MeasureTheory
open scoped ContDiff
namespace KsIndex.Trace
open KsIndex.WeakH1

/-- A real radial profile times an arbitrary signed angular Fourier mode.
Smoothness and compact support are established below under their respective hypotheses. -/
def compactPolarTest (χ : ℝ → ℝ) (n : ℤ) (z : ℂ) : ℂ :=
  (χ ‖z‖ : ℂ) * fourierAmbient n (nUnit z)

lemma compactPolarTest_split (χ : ℝ → ℝ) (n : ℤ) :
    compactPolarTest χ n = fun z =>
      (polarTest χ (fun w => (fourierAmbient n w).re) z : ℂ) +
        Complex.I * (polarTest χ (fun w => (fourierAmbient n w).im) z : ℂ) := by
  funext z
  apply Complex.ext <;> simp [compactPolarTest, polarTest, angExt]

lemma compactPolarTest_smooth {a b : ℝ} (ha : 0 < a) {χ : ℝ → ℝ}
    (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hχs : tsupport χ ⊆ Ioo a b) (n : ℤ) :
    ContDiff ℝ (⊤ : ℕ∞) (compactPolarTest χ n) := by
  rw [compactPolarTest_split]
  have hr := contDiff_polarTest ha hχ hχs
    (Complex.reCLM.contDiff.comp (contDiff_fourierAmbient n))
  have hi := contDiff_polarTest ha hχ hχs
    (Complex.imCLM.contDiff.comp (contDiff_fourierAmbient n))
  exact (Complex.ofRealCLM.contDiff.comp hr).add
    (contDiff_const.mul (Complex.ofRealCLM.contDiff.comp hi))

lemma compactPolarTest_tsupport (χ : ℝ → ℝ) (n : ℤ) :
    tsupport (compactPolarTest χ n) ⊆ (fun z : ℂ => ‖z‖) ⁻¹' tsupport χ := by
  apply closure_minimal _ (IsClosed.preimage continuous_norm isClosed_closure)
  intro z hz
  by_contra hn
  exact hz (by simp [compactPolarTest, image_eq_zero_of_notMem_tsupport hn])

lemma compactPolarTest_hasCompactSupport {χ : ℝ → ℝ} (hc : HasCompactSupport χ) (n : ℤ) :
    HasCompactSupport (compactPolarTest χ n) := by
  obtain ⟨M, hM⟩ := hc.isBounded.subset_closedBall 0
  apply HasCompactSupport.intro (isCompact_closedBall (0 : ℂ) M)
  intro z hz
  apply image_eq_zero_of_notMem_tsupport
  intro hm
  have h := hM (compactPolarTest_tsupport χ n hm)
  apply hz
  simpa only [Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs,
    abs_of_nonneg (norm_nonneg z)] using h

lemma compactPolarTest_annular_support {a b : ℝ} {χ : ℝ → ℝ}
    (hχs : tsupport χ ⊆ Ioo a b) (n : ℤ) :
    tsupport (compactPolarTest χ n) ⊆ annulusSet a b := by
  intro z hz
  exact hχs (compactPolarTest_tsupport χ n hz)

lemma compactPolarTest_boundary_zero {a b : ℝ} (hb : b ≤ 1) {χ : ℝ → ℝ}
    (hχs : tsupport χ ⊆ Ioo a b) (n : ℤ) (w : Circle₁) : compactPolarTest χ n w = 0 := by
  have hn : ‖(w : ℂ)‖ = 1 := mem_sphere_zero_iff_norm.mp w.property
  have hz : χ 1 = 0 := image_eq_zero_of_notMem_tsupport (fun h => not_lt_of_ge hb (hχs h).2)
  simp [compactPolarTest, hn, hz]

def compactPolarTestH1 {a b : ℝ} (ha : 0 < a) {χ : ℝ → ℝ}
    (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hχs : tsupport χ ⊆ Ioo a b) (n : ℤ) : ComplexH1 :=
  globalSmoothH1 (compactPolarTest χ n) (compactPolarTest_smooth ha hχ hχs n)

lemma compactPolarTestH1_trace_zero {a b : ℝ} (ha : 0 < a) (hb : b ≤ 1) {χ : ℝ → ℝ}
    (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hχs : tsupport χ ⊆ Ioo a b) (n : ℤ) :
    diskTraceCLM (compactPolarTestH1 ha hχ hχs n) = 0 := by
  apply Lp.ext
  have h := globalSmoothH1_trace (compactPolarTest χ n) (compactPolarTest_smooth ha hχ hχs n)
  filter_upwards [h, Lp.coeFn_zero ℂ 2 circleMeasure] with w hw hz
  exact hw.trans ((compactPolarTest_boundary_zero hb hχs n w).trans hz.symm)

lemma compactPolarTestH1_zeroTrace {a b : ℝ} (ha : 0 < a) (hb : b ≤ 1) {χ : ℝ → ℝ}
    (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hχs : tsupport χ ⊆ Ioo a b) (n : ℤ) (A : Set Circle₁) :
    compactPolarTestH1 ha hχ hχs n ∈ zeroTraceDomain A := by
  change boundaryRestrictCLM A (diskTraceCLM (compactPolarTestH1 ha hχ hχs n)) = 0
  rw [compactPolarTestH1_trace_zero ha hb hχ hχs n, map_zero]

lemma compactPolarTest_slice (χ : ℝ → ℝ) (n : ℤ) {r : ℝ} (hr : 0 < r)
    (w : Circle₁) : compactPolarTest χ n (r • (w : ℂ)) = (χ r : ℂ) * fourierAmbient n w := by
  have hw : ‖(w : ℂ)‖ = 1 := mem_sphere_zero_iff_norm.mp w.property
  have hn : ‖r • (w : ℂ)‖ = r := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hr, hw, mul_one]
  have hu : nUnit (r • (w : ℂ)) = (w : ℂ) := by
    rw [nUnit, hn, smul_smul, inv_mul_cancel₀ hr.ne', one_smul]
  rw [compactPolarTest, hn, hu]

end KsIndex.Trace
