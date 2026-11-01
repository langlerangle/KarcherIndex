module

public import KsIndexLean.KarcherLiftDifferential

@[expose] public section


/-! Smooth structure on the intrinsic periodic lift, pulled back from the
parameter manifold through its local projection homeomorphisms. -/
noncomputable section
open Set Topology
open scoped ContDiff Manifold
namespace KsIndex.KarcherData.HeightLift
variable {P : Type*} [TopologicalSpace P] [ChartedSpace ℂ P]
variable {F : P → PeriodTarget} (hF : Continuous F)

def liftChart (q : HeightLift F) : OpenPartialHomeomorph (HeightLift F) ℂ :=
  ((projection_isLocalHomeomorph hF).localInverseAt q).symm.trans
    (chartAt ℂ (projection q))

lemma liftChart_apply (q r : HeightLift F) : liftChart hF q r = chartAt ℂ (projection q) (projection r) := by
  simp [liftChart]

lemma liftChart_mem (q : HeightLift F) : q ∈ (liftChart hF q).source := by
  simp [liftChart, mem_chart_source]

/-- Pullback atlas on the existing subtype topology. -/
@[instance_reducible]
def liftChartedSpace : ChartedSpace ℂ (HeightLift F) where
  atlas := Set.range (liftChart hF)
  chartAt := liftChart hF
  mem_chart_source := liftChart_mem hF
  chart_mem_atlas q := ⟨q, rfl⟩

lemma liftChart_symm_projection {q : HeightLift F} {z : ℂ}
    (hz : z ∈ (liftChart hF q).target) :
    projection ((liftChart hF q).symm z) = (chartAt ℂ (projection q)).symm z := by
  exact (projection_isLocalHomeomorph hF).apply_localInverseAt_of_mem hz.2

lemma liftChart_transition {q r : HeightLift F} {z : ℂ}
    (hz : z ∈ ((liftChart hF q).symm.trans (liftChart hF r)).source) :
    (liftChart hF r) ((liftChart hF q).symm z) =
      (chartAt ℂ (projection r)) ((chartAt ℂ (projection q)).symm z) := by
  rw [liftChart_apply, liftChart_symm_projection hF hz.1]

/-- Smoothness of the lifted atlas follows from the parameter atlas transitions. -/
theorem liftSmoothManifold [IsManifold 𝓘(ℝ, ℂ) ∞ P] :
    @IsManifold ℝ _ ℂ _ _ ℂ _ 𝓘(ℝ, ℂ) ∞ (HeightLift F) _ (liftChartedSpace hF) := by
  let := liftChartedSpace hF
  apply isManifold_of_contDiffOn
  intro e e' he he'
  obtain ⟨q, rfl⟩ := he
  obtain ⟨r, rfl⟩ := he'
  intro z hz
  simp only [mfld_simps] at hz ⊢
  have hzq : z ∈ (chartAt ℂ (projection q)).target := hz.1.1
  have hzr : (chartAt ℂ (projection q)).symm z ∈ (chartAt ℂ (projection r)).source := by
    have hr := hz.2.2
    simp only [Set.mem_preimage, OpenPartialHomeomorph.symm_symm,
      IsLocalHomeomorph.localInverseAt_symm] at hr
    rwa [liftChart_symm_projection hF hz.1] at hr
  have h1 := (contMDiffOn_chart_symm (I := 𝓘(ℝ, ℂ)) (n := ∞) (x := projection q)).contMDiffAt
    ((chartAt ℂ (projection q)).open_target.mem_nhds hzq)
  have h2 := (contMDiffOn_chart (I := 𝓘(ℝ, ℂ)) (n := ∞) (x := projection r)).contMDiffAt
    ((chartAt ℂ (projection r)).open_source.mem_nhds hzr)
  have hs := (h2.comp z h1).contDiffAt
  apply hs.contDiffWithinAt.congr
  · intro w hw
    exact liftChart_transition hF hw
  · exact liftChart_transition hF hz

/-- In a neighborhood of each lifted chart center, the ambient map is exactly
 the corresponding real strip representative in the base chart. -/
lemma ambient_chart_germ (q : HeightLift F) :
    (ambient ∘ (liftChart hF q).symm) =ᶠ[𝓝 (liftChart hF q q)]
      (stripAmbient F (height q - Real.pi) ∘ (chartAt ℂ (projection q)).symm) := by
  have hq := liftChart_mem hF q
  have ht := (liftChart hF q).map_source hq
  have hc := (liftChart hF q).continuousAt_symm ht
  have hs : ∀ᶠ z in 𝓝 (liftChart hF q q),
      (liftChart hF q).symm z ∈ strip (height q - Real.pi) := by
    apply hc.preimage_mem_nhds
    rw [(liftChart hF q).left_inv hq]
    exact (isOpen_strip _).mem_nhds (mem_centered_strip q)
  filter_upwards [(liftChart hF q).open_target.mem_nhds ht, hs] with z hz hzs
  dsimp only [Function.comp_apply]
  rw [← stripAmbient_projection hzs, liftChart_symm_projection hF hz]

/-- Local real strip differentials give smoothness and immersion on the whole
 lifted manifold. -/
theorem smooth_immersion_of_strip
    (hloc : ∀ p : P, ∀ a : ℝ, F p ∈ (periodProjectionChart a).target →
      let f := stripAmbient F a ∘ (chartAt ℂ p).symm
      ContDiffAt ℝ ∞ f (chartAt ℂ p p) ∧
      Function.Injective (fderiv ℝ f (chartAt ℂ p p))) :
    letI := liftChartedSpace hF
    ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, AmbientTriple) ∞ (ambient (F := F)) ∧
      ∀ q : HeightLift F,
        IsDiffImmersionAt 𝓘(ℝ, ℂ) 𝓘(ℝ, AmbientTriple) ambient q := by
  let := liftChartedSpace hF
  have hall : ∀ q : HeightLift F,
      ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, AmbientTriple) ∞ ambient q ∧
      IsDiffImmersionAt 𝓘(ℝ, ℂ) 𝓘(ℝ, AmbientTriple) ambient q := by
    intro q
    have ht : F (projection q) ∈ (periodProjectionChart (height q - Real.pi)).target := by
      rw [← project_ambient q]
      apply (periodProjectionChart _).map_source
      rw [periodProjectionChart_source]
      exact mem_centered_strip q
    obtain ⟨hs, hi⟩ := hloc (projection q) (height q - Real.pi) ht
    have he := ambient_chart_germ hF q
    rw [liftChart_apply] at he
    have hs' := hs.congr_of_eventuallyEq he
    have hi' : Function.Injective (fderiv ℝ (ambient ∘ (liftChart hF q).symm)
        (chartAt ℂ (projection q) (projection q))) := by
      rw [he.fderiv_eq]
      exact hi
    have hm : ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, AmbientTriple) ∞ ambient q := by
      rw [contMDiffAt_iff_source]
      change ContMDiffWithinAt 𝓘(ℝ, ℂ) 𝓘(ℝ, AmbientTriple) ∞
        (ambient ∘ (liftChart hF q).symm) _ (liftChart hF q q)
      rw [liftChart_apply]
      exact hs'.contMDiffAt.contMDiffWithinAt
    refine ⟨hm, ?_⟩
    have hd := hm.mdifferentiableAt (by simp)
    apply IsDiffImmersionAt.of_injective_of_finiteDimensional
    simp only [mfderiv, ite_eq_left hd, modelWithCornersSelf_coe, Set.range_id,
      fderivWithin_univ]
    have hi'' : Function.Injective
        (fderiv ℝ (writtenInExtChartAt 𝓘(ℝ, ℂ) 𝓘(ℝ, AmbientTriple) q ambient)
          (extChartAt 𝓘(ℝ, ℂ) q q)) := by
      change Function.Injective (fderiv ℝ (ambient ∘ (liftChart hF q).symm)
        (liftChart hF q q))
      rw [liftChart_apply]
      exact hi'
    exact (tangentSpaceCastModel 𝓘(ℝ, AmbientTriple) (ambient q)).symm.injective.comp
      (hi''.comp (tangentSpaceCastModel 𝓘(ℝ, ℂ) q).injective)
  exact ⟨fun q => (hall q).1, fun q => (hall q).2⟩

end KsIndex.KarcherData.HeightLift

namespace KsIndex.KarcherData
open scoped ParameterAtlas PeriodicAmbient

/-- The actual periodic EW carrier is a smooth real surface, with a globally
 smooth ambient parametrization whose differential is injective everywhere.
 Ambient embeddedness and connectedness are not asserted here. -/
theorem exists_smooth_immersed_periodicEWMap {k : ℕ} [h : Fact (2 ≤ k)]
    (b : PuncturedPlane k) :
    ∃ C : PeriodTarget, ∃ hC : Continuous (extendedEWMap h.out b C),
      letI := HeightLift.liftChartedSpace hC
      IsManifold 𝓘(ℝ, ℂ) ∞ (PeriodicEWCarrier h.out b C) ∧
      ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, AmbientTriple) ∞ (HeightLift.ambient (F := extendedEWMap h.out b C)) ∧
      ∀ q : PeriodicEWCarrier h.out b C,
        IsDiffImmersionAt 𝓘(ℝ, ℂ) 𝓘(ℝ, AmbientTriple) HeightLift.ambient q := by
  obtain ⟨C, hC, hloc⟩ := exists_continuous_all_strip_immersions b
  exact ⟨C, hC, HeightLift.liftSmoothManifold hC, HeightLift.smooth_immersion_of_strip hC hloc⟩

end KsIndex.KarcherData
