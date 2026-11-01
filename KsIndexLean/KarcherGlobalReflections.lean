module

public import KsIndexLean.KarcherParameterReflections
public import KsIndexLean.KarcherSymmetryConstants

@[expose] public section


/-! Actual global reflection identities, with based affine constants explicit. -/
noncomputable section
open scoped ContDiff Manifold
open scoped KsIndex.KarcherData.ParameterAtlas KsIndex.KarcherData.PeriodicAmbient
namespace KsIndex.KarcherData

lemma continuous_reflY : Continuous PeriodTarget.reflY := by
  unfold PeriodTarget.reflY
  fun_prop

lemma continuous_reflZ : Continuous PeriodTarget.reflZ := by
  unfold PeriodTarget.reflZ
  fun_prop

/-- Conjugation equivariance holds globally; the affine offset records the chosen basepoint. -/
theorem extendedEWMap_conjugation {k : ℕ} [h : Fact (2 ≤ k)]
    (b : PuncturedPlane k) (C : PeriodTarget)
    (hF : Continuous (extendedEWMap h.out b C)) :
    ∀ p, extendedEWMap h.out b C (parameterConjugation p) =
      descendedIntegral h.out b ⟨starRingEnd ℂ b.val, conjugate_not_puncture b.property⟩ +
        PeriodTarget.reflY (extendedEWMap h.out b C p) := by
  apply extendedEWMap_affine_equivariance b C _ parameterConjugation PeriodTarget.reflY hF
    (continuous_parameterConjugation k) continuous_reflY
  intro w _
  rw [parameterConjugation_finite]
  erw [extendedEWMap_finite,
    descendedIntegral_basepoint h.out b
      ⟨starRingEnd ℂ b.val, conjugate_not_puncture b.property⟩]
  rw [descendedIntegral_conjMap]

lemma inverse_conjugate_not_puncture {k : ℕ} {z : ℂ}
    (hz : z ∉ Surface.punctures k) : (starRingEnd ℂ z)⁻¹ ∉ Surface.punctures k := by
  intro hp
  have h := conj_mem_punctures (inv_mem_punctures hp)
  simp only [inv_inv, starRingEnd_apply, star_star] at h
  exact hz h

/-- Seam reflection equivariance, including the exchanged regular poles. -/
theorem extendedEWMap_seamReflection {k : ℕ} [h : Fact (2 ≤ k)]
    (b : PuncturedPlane k) (hb0 : b.val ≠ 0) (C : PeriodTarget)
    (hF : Continuous (extendedEWMap h.out b C)) :
    ∀ p, extendedEWMap h.out b C (parameterSeamReflection h.out p) =
      descendedIntegral h.out b
        ⟨(starRingEnd ℂ b.val)⁻¹, inverse_conjugate_not_puncture b.property⟩ +
          PeriodTarget.reflZ (extendedEWMap h.out b C p) := by
  apply extendedEWMap_of_based_equivariance b hb0 C
    (fun w => ⟨(starRingEnd ℂ w.val.val)⁻¹, inverse_conjugate_not_puncture w.val.property⟩)
    (parameterSeamReflection h.out) PeriodTarget.reflZ hF
    (continuous_parameterSeamReflection h.out) continuous_reflZ
  · intro w
    exact parameterSeamReflection_finite h.out w.val w.property _
  · intro w
    exact descendedIntegral_reflZMap h.out b w.val hb0 w.property _ _

/-- The ordinary parameter value 1, fixed by both reflections and never an end. -/
def reflectionBasepoint (k : ℕ) : PuncturedPlane k :=
  ⟨1, by norm_num [Surface.punctures]⟩

/-- A single smooth immersed EW map with both reflection constants zero,
obtained by placing the common fixed parameter point 1 at the origin. -/
theorem exists_reflection_normalized_immersion {k : ℕ} [h : Fact (2 ≤ k)] :
    ∃ C : PeriodTarget,
      let F := extendedEWMap h.out (reflectionBasepoint k) C
      ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, AmbientTriple) ∞ F ∧
      (∀ p, IsDiffImmersionAt 𝓘(ℝ, ℂ) 𝓘(ℝ, AmbientTriple) F p) ∧
      (∀ p, F (parameterConjugation p) = PeriodTarget.reflY (F p)) ∧
      (∀ p, F (parameterSeamReflection h.out p) = PeriodTarget.reflZ (F p)) := by
  obtain ⟨C, hs, hi, _⟩ := exists_smooth_immersed_extendedEWMap (reflectionBasepoint k)
  refine ⟨C, hs, hi, ?_, ?_⟩
  · intro p
    have he := extendedEWMap_conjugation (reflectionBasepoint k) C hs.continuous p
    have hb : (⟨starRingEnd ℂ (reflectionBasepoint k).val,
        conjugate_not_puncture (reflectionBasepoint k).property⟩ : PuncturedPlane k) =
        reflectionBasepoint k := by
      apply Subtype.ext
      simp [reflectionBasepoint]
    rw [hb, descendedIntegral_self, zero_add] at he
    exact he
  · intro p
    have he := extendedEWMap_seamReflection (reflectionBasepoint k)
      (by simp [reflectionBasepoint]) C hs.continuous p
    have hb : (⟨(starRingEnd ℂ (reflectionBasepoint k).val)⁻¹,
        inverse_conjugate_not_puncture (reflectionBasepoint k).property⟩ : PuncturedPlane k) =
        reflectionBasepoint k := by
      apply Subtype.ext
      simp [reflectionBasepoint]
    rw [hb, descendedIntegral_self, zero_add] at he
    exact he

end KsIndex.KarcherData
