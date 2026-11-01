module

public import KsIndexLean.KarcherGlobalRotations

@[expose] public section


/-! Translation of the global immersion and algebraic normalization consumers. -/
noncomputable section
open scoped ContDiff Manifold
open scoped KsIndex.KarcherData.PeriodicAmbient KsIndex.KarcherData.ParameterAtlas
namespace KsIndex.KarcherData

/-- Translation in the actual periodic target is smooth. -/
theorem contMDiff_periodTranslation (T : PeriodTarget) :
    ContMDiff 𝓘(ℝ, AmbientTriple) 𝓘(ℝ, AmbientTriple) ∞ (fun p : PeriodTarget => T + p) := by
  intro p
  apply contMDiffAt_of_chart_lift (X := fun q : AmbientTriple => q) (C := T) contDiffAt_id
  exact Filter.EventuallyEq.rfl

/-- Translation preserves nondegenerate differentials in the periodic manifold. -/
theorem isDiffImmersionAt_periodTranslation (T p : PeriodTarget) :
    IsDiffImmersionAt 𝓘(ℝ, AmbientTriple) 𝓘(ℝ, AmbientTriple) (fun q : PeriodTarget => T + q) p := by
  apply isDiffImmersionAt_of_chart_lift (X := fun q : AmbientTriple => q) (C := T)
    contDiffAt_id Filter.EventuallyEq.rfl
  have hid : HasFDerivAt (fun q : AmbientTriple => q)
      (ContinuousLinearMap.id ℝ AmbientTriple) (chartAt AmbientTriple p p) := hasFDerivAt_id _
  rw [hid.fderiv]
  exact Function.injective_id

lemma periodRotate_add (a : ℂ) (p q : PeriodTarget) :
    PeriodTarget.rotate a (p + q) = PeriodTarget.rotate a p + PeriodTarget.rotate a q := by
  ext <;> simp [PeriodTarget.rotate, mul_add, add_mul] <;> ring

/-- Translating the origin changes a rotation-type affine offset by T - R(T). -/
theorem translated_rotation_identity {M : Type*} (F : M → PeriodTarget) (τ : M → M)
    (a : ℂ) (D T Q : PeriodTarget)
    (he : ∀ p, F (τ p) = D + PeriodTarget.rotate a (F p))
    (hc : D + T - PeriodTarget.rotate a T = Q) :
    ∀ p, T + F (τ p) = Q + PeriodTarget.rotate a (T + F p) := by
  intro p
  rw [he, periodRotate_add, ← hc]
  abel

/-- A horizontal x-axis translation preserves both zero-constant reflection identities. -/
theorem translated_reflection_identities {M : Type*} (F : M → PeriodTarget)
    (τy τz : M → M) (t : ℝ)
    (hy : ∀ p, F (τy p) = PeriodTarget.reflY (F p))
    (hz : ∀ p, F (τz p) = PeriodTarget.reflZ (F p)) :
    (∀ p, (t, 0, 0) + F (τy p) = PeriodTarget.reflY ((t, 0, 0) + F p)) ∧
    (∀ p, (t, 0, 0) + F (τz p) = PeriodTarget.reflZ ((t, 0, 0) + F p)) := by
  constructor
  · intro p
    rw [hy]
    simp [PeriodTarget.reflY]
  · intro p
    rw [hz]
    simp [PeriodTarget.reflZ]

/-- Translating a smooth differential immersion preserves both properties. -/
theorem translated_smooth_immersion {k : ℕ} [Fact (2 ≤ k)]
    (F : ParameterSphere k → PeriodTarget) (T : PeriodTarget)
    (hs : ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, AmbientTriple) ∞ F)
    (hi : ∀ p, IsDiffImmersionAt 𝓘(ℝ, ℂ) 𝓘(ℝ, AmbientTriple) F p) :
    ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, AmbientTriple) ∞ (fun p => T + F p) ∧
      ∀ p, IsDiffImmersionAt 𝓘(ℝ, ℂ) 𝓘(ℝ, AmbientTriple) (fun p => T + F p) p := by
  exact ⟨(contMDiff_periodTranslation T).comp hs,
    fun p => (isDiffImmersionAt_periodTranslation T (F p)).comp (hi p)⟩

/-- Normalize the affine symmetries using two prescribed constant equations.
The equations are explicit hypotheses; this theorem does not compute their constants. -/
theorem normalize_affine_symmetries {k : ℕ} [Fact (2 ≤ k)]
    (F : ParameterSphere k → PeriodTarget)
    (τy τz τr τs : ParameterSphere k → ParameterSphere k)
    (a β : ℂ) (Dr Ds : PeriodTarget) (t : ℝ)
    (hs : ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, AmbientTriple) ∞ F)
    (hi : ∀ p, IsDiffImmersionAt 𝓘(ℝ, ℂ) 𝓘(ℝ, AmbientTriple) F p)
    (hy : ∀ p, F (τy p) = PeriodTarget.reflY (F p))
    (hz : ∀ p, F (τz p) = PeriodTarget.reflZ (F p))
    (hr : ∀ p, F (τr p) = Dr + PeriodTarget.rotate a (F p))
    (hsc : ∀ p, F (τs p) = Ds + PeriodTarget.rotate β (F p))
    (hDr : Dr + (t, 0, 0) - PeriodTarget.rotate a (t, 0, 0) = 0)
    (hDs : Ds + (t, 0, 0) - PeriodTarget.rotate β (t, 0, 0) =
      (0, 0, (Real.pi : AddCircle (2 * Real.pi)))) :
    let G := fun p => (t, 0, 0) + F p
    ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, AmbientTriple) ∞ G ∧
    (∀ p, IsDiffImmersionAt 𝓘(ℝ, ℂ) 𝓘(ℝ, AmbientTriple) G p) ∧
    (∀ p, G (τy p) = PeriodTarget.reflY (G p)) ∧
    (∀ p, G (τz p) = PeriodTarget.reflZ (G p)) ∧
    (∀ p, G (τr p) = PeriodTarget.rotate a (G p)) ∧
    (∀ p, G (τs p) = (0, 0, (Real.pi : AddCircle (2 * Real.pi))) + PeriodTarget.rotate β (G p)) := by
  have hg := translated_smooth_immersion F (t, 0, 0) hs hi
  have href := translated_reflection_identities F τy τz t hy hz
  refine ⟨hg.1, hg.2, href.1, href.2, ?_, ?_⟩
  · intro p
    simpa only [zero_add] using translated_rotation_identity F τr a Dr (t, 0, 0) 0 hr hDr p
  · exact translated_rotation_identity F τs β Ds (t, 0, 0) _ hsc hDs

end KsIndex.KarcherData
