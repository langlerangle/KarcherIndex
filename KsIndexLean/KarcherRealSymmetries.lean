module

public import KsIndexLean.KarcherPaperNormalization

@[expose] public section


/-! Exact real-height symmetry lifts of the normalized EW construction. -/
noncomputable section
namespace KsIndex.KarcherData
open scoped ContDiff Manifold ParameterAtlas PeriodicAmbient
namespace PaperHalfPeriodRealization

variable {k : ℕ} [h : Fact (2 ≤ k)]

/-- The paper's screw on the intrinsic carrier selects the exact +π sheet. -/
def screwLift (R : PaperHalfPeriodRealization k)
    (q : PeriodicEWCarrier h.out (reflectionBasepoint k) R.C) :
    PeriodicEWCarrier h.out (reflectionBasepoint k) R.C :=
  ⟨(parameterScrew h.out (-Real.pi / k) (paper_screw_root h.out) (HeightLift.projection q),
      HeightLift.height q + Real.pi), by
    have he := congrArg (fun p : PeriodTarget => p.2.2) (R.symmetries.2.2.1 (HeightLift.projection q))
    change (Real.pi : AddCircle (2 * Real.pi)) +
        (extendedEWMap h.out (reflectionBasepoint k) R.C
          (parameterScrew h.out (-Real.pi / k) (paper_screw_root h.out) (HeightLift.projection q))).2.2 =
      (Real.pi : AddCircle (2 * Real.pi)) + ((Real.pi : AddCircle (2 * Real.pi)) +
        (extendedEWMap h.out (reflectionBasepoint k) R.C (HeightLift.projection q)).2.2) at he
    have hv := add_left_cancel he
    have hq : (HeightLift.height q : AddCircle (2 * Real.pi)) =
        (extendedEWMap h.out (reflectionBasepoint k) R.C (HeightLift.projection q)).2.2 := q.property
    dsimp only [Prod.fst, Prod.snd]
    rw [AddCircle.coe_add, hq, hv]
    exact add_comm _ _⟩

lemma screwLift_projection (R : PaperHalfPeriodRealization k)
    (q : PeriodicEWCarrier h.out (reflectionBasepoint k) R.C) :
    HeightLift.projection (R.screwLift q) =
      parameterScrew h.out (-Real.pi / k) (paper_screw_root h.out) (HeightLift.projection q) := rfl

lemma screwLift_height (R : PaperHalfPeriodRealization k)
    (q : PeriodicEWCarrier h.out (reflectionBasepoint k) R.C) :
    HeightLift.height (R.screwLift q) + Real.pi =
      (HeightLift.height q + Real.pi) + Real.pi := rfl

lemma continuous_screwLift (R : PaperHalfPeriodRealization k) : Continuous R.screwLift := by
  apply Continuous.subtype_mk
  exact ((continuous_parameterScrew h.out (-Real.pi / k) (paper_screw_root h.out)).comp
    HeightLift.continuous_projection).prodMk (HeightLift.continuous_height.add continuous_const)

/-- Projected ambient equality together with exact real height fixes the actual
 screw action in Euclidean space, without ambient injectivity. -/
lemma screwLift_ambient (R : PaperHalfPeriodRealization k)
    (q : PeriodicEWCarrier h.out (reflectionBasepoint k) R.C) :
    centeredLiftAmbient R.C R.t (R.screwLift q) =
      ((PeriodTarget.rotate (Complex.exp ((-Real.pi / k : ℝ) * Complex.I))
          (projectPeriod (centeredLiftAmbient R.C R.t q))).1,
       (PeriodTarget.rotate (Complex.exp ((-Real.pi / k : ℝ) * Complex.I))
          (projectPeriod (centeredLiftAmbient R.C R.t q))).2.1,
       (centeredLiftAmbient R.C R.t q).2.2 + Real.pi) := by
  have he := R.symmetries.2.2.1 (HeightLift.projection q)
  have hp : projectPeriod (centeredLiftAmbient R.C R.t (R.screwLift q)) =
      (0, 0, (Real.pi : AddCircle (2 * Real.pi))) +
        PeriodTarget.rotate (Complex.exp ((-Real.pi / k : ℝ) * Complex.I))
          (projectPeriod (centeredLiftAmbient R.C R.t q)) := by
    rw [project_centeredLiftAmbient, project_centeredLiftAmbient, screwLift_projection]
    exact he
  apply Prod.ext
  · have hx := congrArg (fun p : PeriodTarget => p.1) hp
    simpa only [projectPeriod, Prod.fst_add, zero_add] using hx
  · apply Prod.ext
    · have hy := congrArg (fun p : PeriodTarget => p.2.1) hp
      simpa only [projectPeriod, Prod.snd_add, Prod.fst_add, zero_add] using hy
    · exact R.screwLift_height q

/-- Two screws followed by minus one period select the height-preserving rotation. -/
def rotationLift (R : PaperHalfPeriodRealization k)
    (q : PeriodicEWCarrier h.out (reflectionBasepoint k) R.C) :=
  HeightLift.deck (-1) (R.screwLift (R.screwLift q))

lemma rotationLift_height (R : PaperHalfPeriodRealization k)
    (q : PeriodicEWCarrier h.out (reflectionBasepoint k) R.C) :
    HeightLift.height (R.rotationLift q) = HeightLift.height q := by
  change (HeightLift.height q + Real.pi + Real.pi) + ((-1 : ℤ) : ℝ) * (2 * Real.pi) = _
  push_cast
  ring

lemma rotationLift_projection (R : PaperHalfPeriodRealization k)
    (q : PeriodicEWCarrier h.out (reflectionBasepoint k) R.C) :
    HeightLift.projection (R.rotationLift q) =
      parameterRotation (-2 * Real.pi / k)
        (by rw [two_mul, pow_add, paper_rotation_root h.out, one_mul]) (HeightLift.projection q) := by
  change parameterScrew h.out (-Real.pi / k) (paper_screw_root h.out)
    (parameterScrew h.out (-Real.pi / k) (paper_screw_root h.out) (HeightLift.projection q)) = _
  rw [parameterScrew_square]
  have ha : (-Real.pi / k : ℝ) + (-Real.pi / k) = -2 * Real.pi / k := by ring
  simp only [ha]

lemma continuous_rotationLift (R : PaperHalfPeriodRealization k) : Continuous R.rotationLift :=
  (HeightLift.continuous_deck (-1)).comp (R.continuous_screwLift.comp R.continuous_screwLift)

lemma rotationLift_ambient (R : PaperHalfPeriodRealization k)
    (q : PeriodicEWCarrier h.out (reflectionBasepoint k) R.C) :
    centeredLiftAmbient R.C R.t (R.rotationLift q) =
      ((PeriodTarget.rotate (Complex.exp ((-2 * Real.pi / k : ℝ) * Complex.I))
          (projectPeriod (centeredLiftAmbient R.C R.t q))).1,
       (PeriodTarget.rotate (Complex.exp ((-2 * Real.pi / k : ℝ) * Complex.I))
          (projectPeriod (centeredLiftAmbient R.C R.t q))).2.1,
       (centeredLiftAmbient R.C R.t q).2.2) := by
  have hp : projectPeriod (centeredLiftAmbient R.C R.t (R.rotationLift q)) =
      PeriodTarget.rotate (Complex.exp ((-2 * Real.pi / k : ℝ) * Complex.I))
        (projectPeriod (centeredLiftAmbient R.C R.t q)) := by
    rw [project_centeredLiftAmbient, project_centeredLiftAmbient, rotationLift_projection]
    exact R.symmetries.2.2.2 (HeightLift.projection q)
  apply Prod.ext
  · have hx := congrArg (fun p : PeriodTarget => p.1) hp
    simpa only [projectPeriod] using hx
  · apply Prod.ext
    · have hy := congrArg (fun p : PeriodTarget => p.2.1) hp
      simpa only [projectPeriod] using hy
    · change HeightLift.height (R.rotationLift q) + Real.pi = HeightLift.height q + Real.pi
      rw [rotationLift_height]

/-- The translated real immersion retains the smoothness and injective
 differential of the certified raw EW lift on exactly the same atlas. -/
theorem centered_geometry (R : PaperHalfPeriodRealization k) :
    let := HeightLift.liftChartedSpace R.hC
    ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, AmbientTriple) ∞ (centeredLiftAmbient (k := k) R.C R.t) ∧
      ∀ q : PeriodicEWCarrier h.out (reflectionBasepoint k) R.C,
        IsDiffImmersionAt 𝓘(ℝ, ℂ) 𝓘(ℝ, AmbientTriple) (centeredLiftAmbient (k := k) R.C R.t) q := by
  let := HeightLift.liftChartedSpace R.hC
  have he : centeredLiftAmbient (k := k) R.C R.t = fun q =>
      ((R.t, 0, Real.pi) : AmbientTriple) + HeightLift.ambient q := by
    funext q
    apply Prod.ext (by rfl)
    apply Prod.ext
    · simp [centeredLiftAmbient, HeightLift.ambient]
    · exact add_comm _ _
  rw [he]
  refine ⟨contMDiff_const.add R.geometry.2.1, ?_⟩
  intro q
  have ht : IsDiffImmersionAt 𝓘(ℝ, AmbientTriple) 𝓘(ℝ, AmbientTriple)
      (fun p : AmbientTriple => (R.t, 0, Real.pi) + p) (HeightLift.ambient q) := by
    have hd : HasFDerivAt (fun p : AmbientTriple => (R.t, 0, Real.pi) + p)
        (ContinuousLinearMap.id ℝ AmbientTriple) (HeightLift.ambient q) :=
      (hasFDerivAt_id (HeightLift.ambient q)).const_add (R.t, 0, Real.pi)
    have hdi : Function.Injective (fderiv ℝ (fun p : AmbientTriple => (R.t, 0, Real.pi) + p)
        (HeightLift.ambient q)) := by
      rw [hd.fderiv]
      exact Function.injective_id
    apply IsDiffImmersionAt.of_injective_of_finiteDimensional
    simp only [mfderiv, ite_eq_left hd.differentiableAt.mdifferentiableAt,
      modelWithCornersSelf_coe, Set.range_id, fderivWithin_univ]
    exact (tangentSpaceCastModel 𝓘(ℝ, AmbientTriple)
      ((R.t, 0, Real.pi) + HeightLift.ambient q)).symm.injective.comp
      (hdi.comp (tangentSpaceCastModel 𝓘(ℝ, AmbientTriple) (HeightLift.ambient q)).injective)
  exact ht.comp (R.geometry.2.2 q)

end PaperHalfPeriodRealization
end KsIndex.KarcherData
