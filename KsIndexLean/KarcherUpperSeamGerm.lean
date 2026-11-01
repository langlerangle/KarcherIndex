module

public import KsIndexLean.KarcherLowerSeamFormula

@[expose] public section


/-! The upper-seam formula holds as a germ in the actual quotient atlas. -/
noncomputable section
open Set Topology
open scoped ContDiff Manifold
namespace KsIndex.KarcherData
open scoped ParameterAtlas
variable {k m : ℕ} [h : Fact (2 ≤ k)] [NeZero m]

lemma finite_parameter_chart_germ (w : PuncturedPlane k) :
    ∀ᶠ z in 𝓝 w.val, ∃ hz : z ∉ Surface.punctures k,
      (chartAt ℂ (finiteParameter w)).symm z = finiteParameter ⟨z,hz⟩ := by
  have hc : IsClosed (Surface.punctures k) :=
    isClosed_eq (continuous_id.pow (2*k)) continuous_const
  filter_upwards [ParameterAtlas.finite_chart_inverse_germ w,
    hc.isOpen_compl.mem_nhds w.property] with z hz hn
  exact ⟨hn, Subtype.ext hz⟩

namespace PaperHalfPeriodRealization
lemma upperSeam_glue_germ (R : PaperHalfPeriodRealization k)
    (f : HeightLift.PeriodQuotient (extendedEWMap h.out (reflectionBasepoint k) R.C) m → ℂ)
    (j : ℤ) (q : PeriodicEWCarrier h.out (reflectionBasepoint k) R.C)
    (w : PuncturedPlane k) (hq : q ∈ R.upperSeamBand j)
    (hp : HeightLift.projection q = finiteParameter w) :
    (f ∘ (HeightLift.periodChart R.hC m (HeightLift.periodQuotientMap m q)).symm)
      =ᶠ[𝓝 w.val] Surface.glue (encodeDiskFunction (R.diskFunctionPullback f))
        (evenCopyIndex (j : ZMod m)) := by
  let Q := HeightLift.periodQuotientMap (F := extendedEWMap h.out (reflectionBasepoint k) R.C) m
  let q₀ := Q q
  let e := HeightLift.periodChart R.hC m q₀
  let l := (HeightLift.periodQuotientMap_isLocalHomeomorph R.hC m).localInverseAt q
  have hl : l q₀ = q :=
    (HeightLift.periodQuotientMap_isLocalHomeomorph R.hC m).localInverseAt_apply_self
  have hec : e q₀ = w.val := by
    rw [HeightLift.periodChart_apply]
    change chartAt ℂ (HeightLift.projection q) (HeightLift.projection q) = _
    rw [hp, ParameterAtlas.parameter_chartAt_finite]
  have hqt : w.val ∈ e.target := hec ▸ e.map_source (HeightLift.periodChart_mem R.hC m q₀)
  have hei : e.symm w.val = q₀ := by
    rw [← hec]
    exact e.left_inv (HeightLift.periodChart_mem R.hC m q₀)
  have hlc : ContinuousAt l q₀ := l.continuousAt
    (HeightLift.periodQuotientMap_isLocalHomeomorph R.hC m).apply_self_mem_localInverseAt_source
  have hcomp : ContinuousAt (l ∘ e.symm) w.val := by
    have hlc' : ContinuousAt l (e.symm w.val) := by simpa only [hei] using hlc
    exact hlc'.comp (e.continuousAt_symm hqt)
  have hband : ∀ᶠ z in 𝓝 w.val, l (e.symm z) ∈ R.upperSeamBand j := by
    apply hcomp.preimage_mem_nhds
    change R.upperSeamBand j ∈ 𝓝 (l (e.symm w.val))
    rw [hei, hl]
    exact (R.isOpen_upperSeamBand j).mem_nhds hq
  have hsource : ∀ᶠ z in 𝓝 w.val, e.symm z ∈ l.source := by
    apply (e.continuousAt_symm hqt).preimage_mem_nhds
    rw [hei]
    exact l.open_source.mem_nhds
      (HeightLift.periodQuotientMap_isLocalHomeomorph R.hC m).apply_self_mem_localInverseAt_source
  filter_upwards [hband, hsource, e.open_target.mem_nhds hqt,
    finite_parameter_chart_germ w] with z hz hs ht hparam
  obtain ⟨hn, hparam⟩ := hparam
  have hQl : Q (l (e.symm z)) = e.symm z :=
    (HeightLift.periodQuotientMap_isLocalHomeomorph R.hC m).apply_localInverseAt_of_mem hs
  have hproj : HeightLift.projection (l (e.symm z)) = finiteParameter ⟨z,hn⟩ := by
    have heproj := congrArg (HeightLift.quotientProjection m) hQl
    change HeightLift.projection (l (e.symm z)) = HeightLift.quotientProjection m (e.symm z) at heproj
    rw [heproj, HeightLift.periodChart_symm_projection R.hC m ht]
    change (chartAt ℂ (HeightLift.projection q)).symm z = _
    rw [hp]
    exact hparam
  have hf := R.upperSeamBand_glue_formula f j (l (e.symm z)) ⟨z,hn⟩ hz hproj
  change f (Q (l (e.symm z))) = _ at hf
  rw [hQl] at hf
  exact hf

/-- In an upper-seam neighborhood, actual smoothness is exactly smoothness
of the paper's glued disk expression. -/
lemma contMDiffAt_iff_upperSeam_glue (R : PaperHalfPeriodRealization k)
    (f : HeightLift.PeriodQuotient (extendedEWMap h.out (reflectionBasepoint k) R.C) m → ℂ)
    (j : ℤ) (q : PeriodicEWCarrier h.out (reflectionBasepoint k) R.C)
    (w : PuncturedPlane k) (hq : q ∈ R.upperSeamBand j)
    (hp : HeightLift.projection q = finiteParameter w) :
    letI := HeightLift.periodChartedSpace R.hC m
    ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ f (HeightLift.periodQuotientMap m q) ↔
      ContDiffAt ℝ ∞ (Surface.glue (encodeDiskFunction (R.diskFunctionPullback f))
        (evenCopyIndex (j : ZMod m))) w.val := by
  letI := HeightLift.periodChartedSpace R.hC m
  rw [contMDiffAt_iff_source]
  have hc : HeightLift.periodChart R.hC m (HeightLift.periodQuotientMap m q)
      (HeightLift.periodQuotientMap m q) = w.val := by
    rw [HeightLift.periodChart_apply]
    change chartAt ℂ (HeightLift.projection q) (HeightLift.projection q) = _
    rw [hp, ParameterAtlas.parameter_chartAt_finite]
  simp only [modelWithCornersSelf_coe, Set.range_id] at ⊢
  change ContMDiffWithinAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞
    (f ∘ (HeightLift.periodChart R.hC m (HeightLift.periodQuotientMap m q)).symm)
    Set.univ (HeightLift.periodChart R.hC m (HeightLift.periodQuotientMap m q)
      (HeightLift.periodQuotientMap m q)) ↔ _
  rw [contMDiffWithinAt_univ, contMDiffAt_iff_contDiffAt, hc]
  have hg := R.upperSeam_glue_germ f j q w hq hp
  exact ⟨fun hf => hf.congr_of_eventuallyEq hg.symm,
    fun hf => hf.congr_of_eventuallyEq hg⟩

end PaperHalfPeriodRealization
end KsIndex.KarcherData
