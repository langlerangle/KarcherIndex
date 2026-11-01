module

public import KsIndexLean.NormalPolynomialAmbient

@[expose] public section


noncomputable section
open Set MeasureTheory
open scoped ContDiff
namespace KsIndex.Trace
open KsIndex.WeakH1 KsIndex.Spherical

lemma weighted_normal_test_pairing (P : C(Circle₁, ℂ)) (G : ℂ → ℂ)
    (hG : ContDiff ℝ ∞ G) (hGP : ∀ w : Circle₁, G w = P w)
    (η : ℂ → ℝ) (hη : ContDiff ℝ ∞ η) :
    inner ℂ (ContinuousMap.toLp 2 circleMeasure ℂ P)
      (diskTraceCLM (globalSmoothH1 (fun z => (η z : ℂ) * G z)
        ((Complex.ofRealCLM.contDiff.comp hη).mul hG))) =
      ((∫ w : Circle₁, η w * ‖P w‖ ^ 2 ∂circleMeasure : ℝ) : ℂ) := by
  rw [L2.inner_def]
  trans ∫ w : Circle₁, ((η w * ‖P w‖ ^ 2 : ℝ) : ℂ) ∂circleMeasure
  swap
  · exact integral_ofReal
  apply integral_congr_ae
  filter_upwards [ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℂ) circleMeasure P,
    globalSmoothH1_trace (fun z => (η z : ℂ) * G z)
      ((Complex.ofRealCLM.contDiff.comp hη).mul hG)] with w hw hv
  simp only [RCLike.inner_apply, hw, hv, hGP, Complex.ofReal_mul, Complex.ofReal_pow]
  calc
    _ = (η w : ℂ) * ((P w) * (starRingEnd ℂ) (P w)) := by ring
    _ = _ := by rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, Complex.ofReal_pow]

/-- A vanishing weak residual for the weighted normal-polynomial test forces
normal data to vanish wherever the weight is positive. -/
theorem sphericalEigen_normal_zero_of_weighted_test
    (k : ℕ) (lam : ℝ) (u : ComplexH1) (ht : u ∈ zeroTraceDomain Set.univ)
    (hu : ∀ v ∈ zeroTraceDomain Set.univ, weakJacobi (surfacePotential k) u v =
      (lam : ℂ) * inner ℂ (weightedDiskValueCLM u) (weightedDiskValueCLM v))
    (G : ℂ → ℂ) (hG : ContDiff ℝ ∞ G)
    (hGP : ∀ w : Circle₁, G w = dirichletNormalPolynomial k lam u ht hu w)
    (η : ℂ → ℝ) (hη : ContDiff ℝ ∞ η) (hη0 : ∀ w : Circle₁, 0 ≤ η w)
    (hz : weakJacobi (sphericalEigenPotential (surfacePotential k) lam) u
      (globalSmoothH1 (fun z => (η z : ℂ) * G z) ((Complex.ofRealCLM.contDiff.comp hη).mul hG)) = 0) :
    ∀ w : Circle₁, 0 < η w → dirichletNormalPolynomial k lam u ht hu w = 0 := by
  rw [sphericalEigen_dirichlet_normal_weak_green k lam u ht hu,
    weighted_normal_test_pairing _ G hG hGP η hη] at hz
  exact circle_weighted_norm_zero _ (fun w : Circle₁ => η w) (hη.continuous.comp continuous_subtype_val) hη0
    (Complex.ofReal_eq_zero.mp hz)

end KsIndex.Trace
