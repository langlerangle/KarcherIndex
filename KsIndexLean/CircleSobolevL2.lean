module

public import KsIndexLean.CircleSobolev
public import KsIndexLean.CircleFourierTransport

@[expose] public section


/-! Realize nonnegative-order coefficient Sobolev spaces on the existing circle. -/
noncomputable section
open MeasureTheory
namespace KsIndex.CircleSobolev
open KsIndex.Trace

@[simp] lemma coeff_zero_order (u : Space 0) (n : ℤ) : coeff 0 u n = u n := by
  simp [coeff, weight]

/-- Realization on the same circle and measure used by diskTraceCLM. -/
def toL2 {s : ℝ} (hs : 0 ≤ s) : Space s →L[ℂ] Lp ℂ 2 circleMeasure :=
  circleFourierCLE.symm.toContinuousLinearMap.comp (inclusionCLM hs)

/-- Physical coefficients are preserved by realization. -/
theorem fourierCoeff_toL2 {s : ℝ} (hs : 0 ≤ s) (u : Space s) (n : ℤ) :
    circleFourierCoeff (toL2 hs u) n = coeff s u n := by
  change circleFourierCoeff (circleFourierCLE.symm (inclusion hs u)) n = _
  rw [circleFourierCoeff_inverse, ← coeff_zero_order, coeff_inclusion]

theorem toL2_injective {s : ℝ} (hs : 0 ≤ s) : Function.Injective (toL2 hs) := by
  intro u v h
  apply coeff_injective s
  funext n
  have hh := congrArg (fun f : Lp ℂ 2 circleMeasure => circleFourierCoeff f n) h
  simpa only [fourierCoeff_toL2] using hh

/-- Exactly the L² functions with the required Fourier summability are realized. -/
theorem mem_range_toL2_iff {s : ℝ} (hs : 0 ≤ s) (f : Lp ℂ 2 circleMeasure) :
    f ∈ Set.range (toL2 hs) ↔
      Summable (fun n : ℤ => (1 + |(n : ℝ)|) ^ (2 * s) * ‖circleFourierCoeff f n‖ ^ 2) := by
  constructor
  · rintro ⟨u, rfl⟩
    simp only [fourierCoeff_toL2]
    exact (exists_coeff_iff s (coeff s u)).mp ⟨u, rfl⟩
  · intro hf
    obtain ⟨u, hu⟩ := (exists_coeff_iff s (circleFourierCoeff f)).mpr hf
    refine ⟨u, circleFourierCLE.injective ?_⟩
    apply Subtype.ext
    funext n
    simp only [circleFourierCLE_apply, fourierCoeff_toL2]
    exact congrFun hu n

/-- On L² representatives, the opposite-order duality is the L² inner product. -/
theorem duality_eq_inner_of_coefficients (s : ℝ) (u : Space (-s)) (v : Space s)
    (f g : Lp ℂ 2 circleMeasure)
    (hf : ∀ n, coeff (-s) u n = circleFourierCoeff f n)
    (hg : ∀ n, coeff s v n = circleFourierCoeff g n) :
    duality s u v = inner ℂ f g := by
  have hp : coefficientDuality s u v = inner ℂ (circleFourierCLE f) (circleFourierCLE g) := by
    rw [coefficientDuality_eq_tsum]
    change _ = ∑' n, inner ℂ (circleFourierCLE f n) (circleFourierCLE g n)
    simp only [hf, hg, circleFourierCLE_apply, RCLike.inner_apply']
  rw [duality, hp, circleFourierCLE_inner, Complex.real_smul, Complex.ofReal_inv]
  simp [← mul_assoc]

/-- Integral agreement uses the existing arclength measure and conjugates FIRST. -/
theorem duality_eq_integral_of_coefficients (s : ℝ) (u : Space (-s)) (v : Space s)
    (f g : Lp ℂ 2 circleMeasure)
    (hf : ∀ n, coeff (-s) u n = circleFourierCoeff f n)
    (hg : ∀ n, coeff s v n = circleFourierCoeff g n) :
    duality s u v = ∫ w, starRingEnd ℂ (f w) * g w ∂circleMeasure := by
  rw [duality_eq_inner_of_coefficients s u v f g hf hg, L2.inner_def]
  simp only [RCLike.inner_apply']

end KsIndex.CircleSobolev
