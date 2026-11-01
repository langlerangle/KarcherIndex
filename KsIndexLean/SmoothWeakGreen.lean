module

public import KsIndexLean.HorizontalWeakGreen
public import KsIndexLean.PolarFourierPairing

@[expose] public section


noncomputable section
open Set MeasureTheory
open scoped ContDiff
namespace KsIndex.Trace
open KsIndex.WeakH1 KsIndex.Surface

/-- Green's boundary flux formula against every weak H1 test. The supplied
L2 flux is required to agree with the actual classical normal derivative. -/
lemma smooth_weak_green_of_flux (V : BoundedRealPotential) (u : ℂ → ℂ)
    (hu : ContDiff ℝ ∞ u)
    (hjac : ∀ w ∈ (WeakH1.disk : Set ℂ), laplacian u w + (V.V w : ℂ) * u w = 0)
    (F : Lp ℂ 2 circleMeasure)
    (hF : (F : Circle₁ → ℂ) =ᵐ[circleMeasure] fun w => fderiv ℝ u w w)
    (v : ComplexH1) :
    weakJacobi V (globalSmoothH1 u hu) v = inner ℂ F (diskTraceCLM v) := by
  have hc : Continuous (fun v : mixedCharacterDomain 1 0 true true =>
      weakJacobi V (globalSmoothH1 u hu) v) :=
    (continuous_weakJacobi_fixed_left V (globalSmoothH1 u hu)).comp continuous_subtype_val
  have hb : Continuous (fun v : mixedCharacterDomain 1 0 true true =>
      inner ℂ F (diskTraceCLM v)) :=
    continuous_const.inner (diskTraceCLM.continuous.comp continuous_subtype_val)
  have he := (naturalCharacterToMixed_denseRange (k := 1) (by decide) 0 true true).equalizer
    hc hb (by
      funext f
      let ff : KsIndex.SingleDisk.NatCc 1 true true := ⟨f.val, f.property.1⟩
      obtain ⟨G, hG, hv, hx, hy, ht⟩ := naturalCoreH1_C1_representative (by decide : 1 ≤ 1) ff
      have hg := weakJacobi_C1_test_green V u G hu hG (naturalCoreH1 (by decide) ff) hv hx hy hjac
      change weakJacobi V (globalSmoothH1 u hu) (naturalCoreH1 (by decide) ff) =
        inner ℂ F (diskTraceCLM (naturalCoreH1 (by decide) ff))
      rw [hg, L2.inner_def]
      apply integral_congr_ae
      filter_upwards [hF, ht] with w hw htw
      simp only [RCLike.inner_apply, hw, htw, mul_comm])
  exact congrFun he ⟨v, mem_trivial_NN_sector v⟩

/-- A weak Neumann solution is orthogonal on the boundary to every smooth
Jacobi solution's normal flux. The first-variable conjugation is explicit. -/
lemma weak_neumann_boundary_flux_orthogonal (V : BoundedRealPotential)
    (v : ComplexH1) (hv : ∀ w : ComplexH1, weakJacobi V v w = 0)
    (u : ℂ → ℂ) (hu : ContDiff ℝ ∞ u)
    (hjac : ∀ w ∈ (WeakH1.disk : Set ℂ), laplacian u w + (V.V w : ℂ) * u w = 0)
    (F : Lp ℂ 2 circleMeasure)
    (hF : (F : Circle₁ → ℂ) =ᵐ[circleMeasure] fun w => fderiv ℝ u w w) :
    inner ℂ F (diskTraceCLM v) = 0 := by
  rw [← smooth_weak_green_of_flux V u hu hjac F hF v, ← weakJacobi_conj,
    hv, map_zero]

/-- A nonzero pure Fourier normal flux excludes the corresponding boundary
coefficient of any full weak Neumann solution. -/
lemma weak_neumann_fourier_trace_zero (V : BoundedRealPotential)
    (v : ComplexH1) (hv : ∀ w : ComplexH1, weakJacobi V v w = 0)
    (u : ℂ → ℂ) (hu : ContDiff ℝ ∞ u)
    (hjac : ∀ w ∈ (WeakH1.disk : Set ℂ), laplacian u w + (V.V w : ℂ) * u w = 0)
    (n : ℤ) (a : ℂ) (ha : a ≠ 0)
    (hflux : ∀ w : Circle₁, fderiv ℝ u w w = a * fourierAmbient n w) :
    circleFourierCoeff (diskTraceCLM v) n = 0 := by
  have hF : ((a • fourierTestLp n : Lp ℂ 2 circleMeasure) : Circle₁ → ℂ)
      =ᵐ[circleMeasure] fun w => fderiv ℝ u w w := by
    filter_upwards [Lp.coeFn_smul a (fourierTestLp n), fourierTestLp_coe n] with w hw hf
    simp only [hw, Pi.smul_apply, smul_eq_mul, hf, hflux]
  have hz := weak_neumann_boundary_flux_orthogonal V v hv u hu hjac (a • fourierTestLp n) hF
  rw [inner_smul_left, fourierTestLp_inner_unscaled] at hz
  have ha' : (starRingEnd ℂ) a ≠ 0 := by simpa using ha
  have hp : ((2 * Real.pi : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (by positivity)
  exact (mul_eq_zero.mp ((mul_eq_zero.mp hz).resolve_left ha')).resolve_left hp

end KsIndex.Trace
