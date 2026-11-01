module

public import KsIndexLean.SphericalEigenBoundaryFluxPairing

@[expose] public section


noncomputable section
open Set MeasureTheory
open scoped ContDiff
namespace KsIndex.Trace
open KsIndex.WeakH1 KsIndex.Spherical

/-- Interior weak solutions give the same boundary residual on tests with
identical actual L2 traces. -/
lemma weakJacobi_eq_of_trace_eq (V : BoundedRealPotential) (u : ComplexH1)
    (hu : ∀ v ∈ zeroTraceDomain Set.univ, weakJacobi V u v = 0)
    (v w : ComplexH1) (hvw : diskTraceCLM v = diskTraceCLM w) :
    weakJacobi V u v = weakJacobi V u w := by
  let L : ComplexH1 →ₗ[ℂ] ℂ :=
    { toFun := weakJacobi V u
      map_add' := weakJacobi_add_right V u
      map_smul' := fun a v => weakJacobi_smul_right V a u v }
  have ht : v - w ∈ zeroTraceDomain Set.univ := by
    rw [mem_fullZeroTrace_iff, map_sub, hvw, sub_self]
  have hz : L (v - w) = 0 := hu _ ht
  rw [map_sub] at hz
  exact sub_eq_zero.mp hz

lemma compactPolarTestH1_trace_eq_fourier {a c : ℝ} (ha : 0 < a)
    {χ : ℝ → ℝ} (hχ : ContDiff ℝ ∞ χ) (hs : tsupport χ ⊆ Ioo a c)
    (hχ1 : χ 1 = 1) (n : ℤ) :
    diskTraceCLM (compactPolarTestH1 ha hχ hs n) =
      diskTraceCLM (globalSmoothH1 (fourierAmbient n) (contDiff_fourierAmbient n)) := by
  apply Lp.ext
  filter_upwards [globalSmoothH1_trace (compactPolarTest χ n) (compactPolarTest_smooth ha hχ hs n),
    globalSmoothH1_trace (fourierAmbient n) (contDiff_fourierAmbient n)] with w hw hv
  change diskTraceCLM (globalSmoothH1 (compactPolarTest χ n) _) w = _
  rw [hw, hv]
  have he := compactPolarTest_slice χ n (by norm_num : (0 : ℝ) < 1) w
  simpa only [one_smul, hχ1, Complex.ofReal_one, one_mul] using he

/-- The normal coefficient can be tested using the canonical smooth Fourier
extension; the radial cutoff used in its derivation disappears. -/
lemma sphericalEigen_fourier_extension_flux_pairing_of_cutoff {a c : ℝ}
    (ha : 0 < a) (ha1 : a < 1) (k : ℕ) (lam : ℝ) (u : ComplexH1) (n : ℤ)
    (hu : ∀ v ∈ zeroTraceDomain Set.univ, weakJacobi (surfacePotential k) u v =
      (lam : ℂ) * inner ℂ (weightedDiskValueCLM u) (weightedDiskValueCLM v))
    {χ : ℝ → ℝ} (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ)
    (hs : tsupport χ ⊆ Ioo a c) (hχ1 : χ 1 = 1) :
    weakJacobi (sphericalEigenPotential (surfacePotential k) lam) u
      (globalSmoothH1 (fourierAmbient n) (contDiff_fourierAmbient n)) =
      ((2 * Real.pi : ℝ) : ℂ) * (starRingEnd ℂ) (eigenDiskNormalMode k lam u n) := by
  rw [← weakJacobi_eq_of_trace_eq _ u
    (fun v hv => (spherical_eigen_equation_iff _ lam u v).mp (hu v hv))
    (compactPolarTestH1 ha hχ hs n) _ (compactPolarTestH1_trace_eq_fourier ha hχ hs hχ1 n)]
  exact sphericalEigen_boundary_fourier_flux_pairing ha ha1 k lam u n hu hχ hc hs hχ1

lemma sphericalEigen_fourier_extension_flux_pairing
    (k : ℕ) (lam : ℝ) (u : ComplexH1) (n : ℤ)
    (hu : ∀ v ∈ zeroTraceDomain Set.univ, weakJacobi (surfacePotential k) u v =
      (lam : ℂ) * inner ℂ (weightedDiskValueCLM u) (weightedDiskValueCLM v)) :
    weakJacobi (sphericalEigenPotential (surfacePotential k) lam) u
      (globalSmoothH1 (fourierAmbient n) (contDiff_fourierAmbient n)) =
      ((2 * Real.pi : ℝ) : ℂ) * (starRingEnd ℂ) (eigenDiskNormalMode k lam u n) := by
  let χ : ContDiffBump (1 : ℝ) := ⟨1 / 8, 1 / 4, by norm_num, by norm_num⟩
  apply sphericalEigen_fourier_extension_flux_pairing_of_cutoff
    (a := 1 / 2) (c := 2) (by norm_num) (by norm_num) k lam u n hu
    χ.contDiff χ.hasCompactSupport
  · rw [χ.tsupport_eq]
    intro r hr
    have h : |r - 1| ≤ (1 / 4 : ℝ) := by
      simpa only [Metric.mem_closedBall, Real.dist_eq] using hr
    have hh := abs_le.mp h
    constructor <;> linarith [hh.1, hh.2]
  · exact χ.one_of_mem_closedBall (by simp [χ])

end KsIndex.Trace
