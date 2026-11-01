module

public import KsIndexLean.FiniteFourierUniqueness
public import KsIndexLean.CircleFourierRotation
public import KsIndexLean.FourierRadialFTC

@[expose] public section


noncomputable section
open Set MeasureTheory
namespace KsIndex.Trace
local instance : Fact (0 < 2 * Real.pi) := ⟨Real.two_pi_pos⟩

def circleFourierModeContinuous (n : ℤ) : C(Circle₁, ℂ) :=
  ⟨fun w => fourierAmbient n w, (contDiff_fourierAmbient n).continuous.comp continuous_subtype_val⟩

lemma circleFourierMode_coefficient (n m : ℤ) :
    circleCoefficientCLM m (ContinuousMap.toLp 2 circleMeasure ℂ (circleFourierModeContinuous n)) =
      if m = n then 1 else 0 := by
  rw [circleCoefficientCLM_apply,
    congrFun (circleFourierCoeff_congr_ae (ContinuousMap.coeFn_toLp circleMeasure (circleFourierModeContinuous n))) m,
    ← fourierCoeff_geometric_pullback]
  have he : (fun x => circleFourierModeContinuous n (fourierCircleHomeomorph x)) = fourier n := by
    funext x
    induction x using QuotientAddGroup.induction_on with
    | H x => exact (fourierCircleHomeomorph_coe x ▸ fourierAmbient_circleParam n x)
  rw [he, fourierCoeff_fourier]
  simp [Pi.single_apply, eq_comm]

/-- A finite Fourier polynomial as an actual continuous boundary function. -/
def circleFourierPolynomial (s : Finset ℤ) (c : ℤ → ℂ) : C(Circle₁, ℂ) :=
  ∑ n ∈ s, c n • circleFourierModeContinuous n

lemma circleFourierPolynomial_apply (s : Finset ℤ) (c : ℤ → ℂ) (w : Circle₁) :
    circleFourierPolynomial s c w = ∑ n ∈ s, c n * fourierAmbient n w := by
  simp [circleFourierPolynomial, circleFourierModeContinuous]

lemma circleFourierPolynomial_coefficient (s : Finset ℤ) (c : ℤ → ℂ) (m : ℤ) :
    circleCoefficientCLM m (ContinuousMap.toLp 2 circleMeasure ℂ (circleFourierPolynomial s c)) =
      if m ∈ s then c m else 0 := by
  simp only [circleFourierPolynomial, map_sum, map_smul, circleFourierMode_coefficient, smul_eq_mul]
  simp [mul_ite]

/-- Finite coefficient support yields equality in the actual geometric L2 space. -/
lemma circleL2_eq_finite_fourier (f : Lp ℂ 2 circleMeasure) (s : Finset ℤ)
    (hs : ∀ n ∉ s, circleFourierCoeff f n = 0) :
    f = ContinuousMap.toLp 2 circleMeasure ℂ (circleFourierPolynomial s (circleFourierCoeff f)) := by
  apply circleFourierCLE.injective
  apply Subtype.ext
  funext n
  change circleFourierCLE f n = circleFourierCLE _ n
  simp only [circleFourierCLE_apply, ← circleCoefficientCLM_apply,
    circleFourierPolynomial_coefficient]
  by_cases hn : n ∈ s
  · simp [hn]
  · simpa [hn, circleCoefficientCLM_apply] using hs n hn

/-- Finite spectral support allows open-arc uniqueness for L2 equivalence classes. -/
theorem circleL2_eq_zero_of_finite_support_open_ae (f : Lp ℂ 2 circleMeasure)
    (hf : {n : ℤ | circleFourierCoeff f n ≠ 0}.Finite)
    (A : Set Circle₁) (hA : IsOpen A) (hne : A.Nonempty)
    (hz : (f : Circle₁ → ℂ) =ᵐ[circleMeasure.restrict A] 0) : f = 0 := by
  let s := hf.toFinset
  have hs : ∀ n ∉ s, circleFourierCoeff f n = 0 := by
    intro n hn
    simpa only [s, Set.Finite.mem_toFinset, Set.mem_ofPred_eq, not_not] using hn
  have he := circleL2_eq_finite_fourier f s hs
  have ha : (f : Circle₁ → ℂ) =ᵐ[circleMeasure] circleFourierPolynomial s (circleFourierCoeff f) := by
    exact (Lp.ext_iff.mp he).trans (ContinuousMap.coeFn_toLp (𝕜 := ℂ)
      circleMeasure (circleFourierPolynomial s (circleFourierCoeff f)))
  have hpoly : (fun w : Circle₁ => ∑ n ∈ s, circleFourierCoeff f n * fourierAmbient n w)
      =ᵐ[circleMeasure.restrict A] 0 := by
    have har := ha.filter_mono (ae_mono (Measure.restrict_le_self (s := A)))
    filter_upwards [har, hz] with w hw hwz
    rw [← circleFourierPolynomial_apply, ← hw, hwz]
  have hall := finite_fourier_eq_zero_of_open_ae s (circleFourierCoeff f) A hA hne hpoly
  apply Lp.ext
  filter_upwards [ha, Lp.coeFn_zero ℂ 2 circleMeasure] with w hw h0
  rw [hw, circleFourierPolynomial_apply, hall, h0]
  rfl

end KsIndex.Trace
