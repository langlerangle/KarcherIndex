module

public import KsIndexLean.KarcherSeamReflectionSmooth

@[expose] public section


/-! Smoothness in reflected lower-seam coordinates on the actual EW quotient. -/
noncomputable section
open Set Topology
open scoped ContDiff Manifold
namespace KsIndex.KarcherData
open scoped ParameterAtlas

namespace HeightLift
variable {P : Type*} [TopologicalSpace P] {F : P → PeriodTarget}

/-- The two local ways of lifting a parameter to the period quotient agree. -/
lemma localInverse_periodQuotient_germ (hF : Continuous F) (m : ℕ) (q : HeightLift F) :
    (periodQuotientMap m ∘ (projection_isLocalHomeomorph hF).localInverseAt q)
      =ᶠ[𝓝 (projection q)]
        (quotientProjection_isLocalHomeomorph hF m).localInverseAt (periodQuotientMap m q) := by
  let l := (projection_isLocalHomeomorph hF).localInverseAt q
  let e := (quotientProjection_isLocalHomeomorph hF m).localInverseAt (periodQuotientMap m q)
  have hl : l (projection q) = q := (projection_isLocalHomeomorph hF).localInverseAt_apply_self
  have hc : ContinuousAt (periodQuotientMap m ∘ l) (projection q) :=
    (periodQuotientMap_isQuotientMap (F := F) m).continuous.continuousAt.comp
      (l.continuousAt (projection_isLocalHomeomorph hF).apply_self_mem_localInverseAt_source)
  have ht : ∀ᶠ p in 𝓝 (projection q), periodQuotientMap m (l p) ∈ e.target := by
    apply hc.preimage_mem_nhds
    change e.target ∈ 𝓝 (periodQuotientMap m (l (projection q)))
    rw [hl]
    exact e.open_target.mem_nhds
      (quotientProjection_isLocalHomeomorph hF m).self_mem_localInverseAt_target
  filter_upwards [ht, l.open_source.mem_nhds
    (projection_isLocalHomeomorph hF).apply_self_mem_localInverseAt_source] with p hp hs
  have hproj : projection (l p) = p :=
    (projection_isLocalHomeomorph hF).apply_localInverseAt_of_mem hs
  have he := e.right_inv hp
  simp only [e, IsLocalHomeomorph.localInverseAt_symm] at he
  change e (projection (l p)) = periodQuotientMap m (l p) at he
  rw [hproj] at he
  exact he.symm
end HeightLift

namespace PaperHalfPeriodRealization
variable {k m : ℕ} [h : Fact (2 ≤ k)] [NeZero m]

lemma contMDiffAt_iff_lowerSeam_glue (R : PaperHalfPeriodRealization k)
    (f : HeightLift.PeriodQuotient (extendedEWMap h.out (reflectionBasepoint k) R.C) m → ℂ)
    (j : ℤ) (q : PeriodicEWCarrier h.out (reflectionBasepoint k) R.C)
    (w : PuncturedPlane k) (hq : q ∈ R.lowerSeamBand j)
    (hp : parameterSeamReflection h.out (HeightLift.projection q) = finiteParameter w) :
    letI := HeightLift.periodChartedSpace R.hC m
    ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ f (HeightLift.periodQuotientMap m q) ↔
      ContDiffAt ℝ ∞ (Surface.glue (encodeDiskFunction (R.diskFunctionPullback f))
        (oddCopyIndex (j : ZMod m))) w.val := by
  letI := HeightLift.periodChartedSpace R.hC m
  let e := (HeightLift.quotientProjection_isLocalHomeomorph R.hC m).localInverseAt
    (HeightLift.periodQuotientMap m q)
  let b := chartAt ℂ (finiteParameter w)
  have hs : parameterSeamReflection h.out (finiteParameter w) = HeightLift.projection q := by
    rw [← hp, parameterSeamReflection_involutive]
  have hb : b (finiteParameter w) = w.val := ParameterAtlas.parameter_chartAt_finite w
  have ht : w.val ∈ b.target := hb ▸ b.map_source (mem_chart_source _ _)
  have hi : b.symm w.val = finiteParameter w := by
    rw [← hb]
    exact b.left_inv (mem_chart_source _ _)
  have hbc : ContinuousAt (fun z => parameterSeamReflection h.out (b.symm z)) w.val :=
    (continuous_parameterSeamReflection h.out).continuousAt.comp (b.continuousAt_symm ht)
  have htend : Filter.Tendsto (fun z => parameterSeamReflection h.out (b.symm z))
      (𝓝 w.val) (𝓝 (HeightLift.projection q)) := by
    change Filter.Tendsto _ _ (𝓝 (parameterSeamReflection h.out (b.symm w.val))) at hbc
    rw [hi, hs] at hbc
    exact hbc
  have hg := (HeightLift.localInverse_periodQuotient_germ R.hC m q).comp_tendsto htend
  have hformula : ((f ∘ e ∘ parameterSeamReflection h.out) ∘ b.symm)
      =ᶠ[𝓝 w.val] Surface.glue (encodeDiskFunction (R.diskFunctionPullback f))
        (oddCopyIndex (j : ZMod m)) := by
    filter_upwards [hg, R.lowerSeam_glue_germ f j q w hq hp] with z hz hf
    change f (e (parameterSeamReflection h.out (b.symm z))) = _
    change HeightLift.periodQuotientMap m (R.lowerParameterLift q w z) =
      e (parameterSeamReflection h.out (b.symm z)) at hz
    rw [← hz]
    exact hf
  rw [HeightLift.contMDiffAt_iff_local_parameter R.hC m]
  change ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ (f ∘ e) (HeightLift.projection q) ↔ _
  rw [← hs, ← contMDiffAt_comp_seamReflection_iff]
  rw [contMDiffAt_iff_source]
  simp only [modelWithCornersSelf_coe, Set.range_id]
  change ContMDiffWithinAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞
    ((f ∘ e ∘ parameterSeamReflection h.out) ∘ b.symm) Set.univ (b (finiteParameter w)) ↔ _
  rw [contMDiffWithinAt_univ, contMDiffAt_iff_contDiffAt, hb]
  exact ⟨fun hf => hf.congr_of_eventuallyEq hformula.symm,
    fun hf => hf.congr_of_eventuallyEq hformula⟩

end PaperHalfPeriodRealization
end KsIndex.KarcherData
