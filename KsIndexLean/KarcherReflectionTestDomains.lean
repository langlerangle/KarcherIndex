module

public import KsIndexLean.KarcherConjugationEncoding
public import KsIndexLean.KarcherHeightReflectionEncoding
public import KsIndexLean.KarcherQuotientSmoothPullback
public import KsIndexLean.SurfaceConjugationPullback

@[expose] public section


/-! Actual reflection pullbacks preserve the compact smooth test domain. -/
noncomputable section
open scoped ContDiff Manifold KsIndex.KarcherData.ParameterAtlas
namespace KsIndex.KarcherData.PaperHalfPeriodRealization
variable {k m : ℕ} [h : Fact (2 ≤ k)] [NeZero m]

lemma compactSmooth_conjugation_pullback (R : PaperHalfPeriodRealization k)
    (f : HeightLift.PeriodQuotient (extendedEWMap h.out (reflectionBasepoint k) R.C) m → ℂ) :
    letI := HeightLift.periodChartedSpace R.hC m
    (ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ f ∧ HasCompactSupport f) →
      ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ (f ∘ R.periodConjugation m) ∧
        HasCompactSupport (f ∘ R.periodConjugation m) := by
  intro hf
  apply (R.compactSmooth_iff_encoding_mem_CcSmooth _).mpr
  rw [R.encode_conjugation_pullback]
  exact SurfaceSym.coordinateConjugation_mem_CcSmooth
    ((R.compactSmooth_iff_encoding_mem_CcSmooth f).mp hf)

lemma compactSmooth_heightReflection_pullback (R : PaperHalfPeriodRealization k)
    (f : HeightLift.PeriodQuotient (extendedEWMap h.out (reflectionBasepoint k) R.C) m → ℂ) :
    letI := HeightLift.periodChartedSpace R.hC m
    (ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ f ∧ HasCompactSupport f) →
      ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ (f ∘ R.periodHeightReflection m) ∧
        HasCompactSupport (f ∘ R.periodHeightReflection m) := by
  letI := HeightLift.periodChartedSpace R.hC m
  intro hf
  have hp : ∀ q, HeightLift.quotientProjection m (R.periodHeightReflection m q) =
      parameterSeamReflection h.out (HeightLift.quotientProjection m q) := by
    intro q
    induction q using Quotient.inductionOn with
    | h q => rfl
  refine ⟨HeightLift.contMDiff_comp_of_parameter_action R.hC m
    (R.periodHeightReflection m) (parameterSeamReflection h.out)
    (R.continuous_periodHeightReflection m) parameterSeamReflection_contMDiff hp f hf.1, ?_⟩
  let e : HeightLift.PeriodQuotient (extendedEWMap h.out (reflectionBasepoint k) R.C) m ≃ₜ
      HeightLift.PeriodQuotient (extendedEWMap h.out (reflectionBasepoint k) R.C) m :=
    { toEquiv := { toFun := R.periodHeightReflection m
                   invFun := R.periodHeightReflection m
                   left_inv := R.periodHeightReflection_involutive m
                   right_inv := R.periodHeightReflection_involutive m }
      continuous_toFun := R.continuous_periodHeightReflection m
      continuous_invFun := R.continuous_periodHeightReflection m }
  exact hf.2.comp_homeomorph e

end KsIndex.KarcherData.PaperHalfPeriodRealization
