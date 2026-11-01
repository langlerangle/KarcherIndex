module

public import KsIndexLean.KarcherUpperSeamGerm

@[expose] public section


/-! The lower-seam expression in a reflected local EW parameter. -/
noncomputable section
open Set Topology
open scoped ContDiff Manifold
namespace KsIndex.KarcherData
open scoped ParameterAtlas
variable {k m : ℕ} [h : Fact (2 ≤ k)] [NeZero m]
namespace PaperHalfPeriodRealization

/-- A local lift of the reflected finite parameter, centered at an actual EW point.
The formula also applies when that point lies over infinity. -/
def lowerParameterLift (R : PaperHalfPeriodRealization k)
    (q : PeriodicEWCarrier h.out (reflectionBasepoint k) R.C) (w : PuncturedPlane k)
    (z : ℂ) : PeriodicEWCarrier h.out (reflectionBasepoint k) R.C :=
  (HeightLift.projection_isLocalHomeomorph R.hC).localInverseAt q
    (parameterSeamReflection h.out ((chartAt ℂ (finiteParameter w)).symm z))

lemma lowerSeam_glue_germ (R : PaperHalfPeriodRealization k)
    (f : HeightLift.PeriodQuotient (extendedEWMap h.out (reflectionBasepoint k) R.C) m → ℂ)
    (j : ℤ) (q : PeriodicEWCarrier h.out (reflectionBasepoint k) R.C)
    (w : PuncturedPlane k) (hq : q ∈ R.lowerSeamBand j)
    (hp : parameterSeamReflection h.out (HeightLift.projection q) = finiteParameter w) :
    (fun z => f (HeightLift.periodQuotientMap m (R.lowerParameterLift q w z)))
      =ᶠ[𝓝 w.val] Surface.glue (encodeDiskFunction (R.diskFunctionPullback f))
        (oddCopyIndex (j : ZMod m)) := by
  let b := chartAt ℂ (finiteParameter w)
  let l := (HeightLift.projection_isLocalHomeomorph R.hC).localInverseAt q
  have hb : b (finiteParameter w) = w.val := ParameterAtlas.parameter_chartAt_finite w
  have ht : w.val ∈ b.target := hb ▸ b.map_source (mem_chart_source _ _)
  have hi : b.symm w.val = finiteParameter w := by
    rw [← hb]
    exact b.left_inv (mem_chart_source _ _)
  have hs : parameterSeamReflection h.out (finiteParameter w) = HeightLift.projection q := by
    rw [← hp, parameterSeamReflection_involutive]
  have he : parameterSeamReflection h.out (b.symm w.val) = HeightLift.projection q := by rw [hi, hs]
  have hl : l (HeightLift.projection q) = q :=
    (HeightLift.projection_isLocalHomeomorph R.hC).localInverseAt_apply_self
  have hbc : ContinuousAt (fun z => parameterSeamReflection h.out (b.symm z)) w.val :=
    (continuous_parameterSeamReflection h.out).continuousAt.comp (b.continuousAt_symm ht)
  have hlc : ContinuousAt l (parameterSeamReflection h.out (b.symm w.val)) := by
    rw [he]
    exact l.continuousAt
      (HeightLift.projection_isLocalHomeomorph R.hC).apply_self_mem_localInverseAt_source
  have hrc : ContinuousAt (R.lowerParameterLift q w) w.val := by
    change ContinuousAt (l ∘ (fun z => parameterSeamReflection h.out (b.symm z))) w.val
    exact ContinuousAt.comp (f := fun z => parameterSeamReflection h.out (b.symm z)) hlc hbc
  have hr : R.lowerParameterLift q w w.val = q := by
    change l (parameterSeamReflection h.out (b.symm w.val)) = q
    rw [he, hl]
  have hband : ∀ᶠ z in 𝓝 w.val, R.lowerParameterLift q w z ∈ R.lowerSeamBand j := by
    apply hrc.preimage_mem_nhds
    rw [hr]
    exact (R.isOpen_lowerSeamBand j).mem_nhds hq
  have hsource : ∀ᶠ z in 𝓝 w.val, parameterSeamReflection h.out (b.symm z) ∈ l.source := by
    apply hbc.preimage_mem_nhds
    rw [he]
    exact l.open_source.mem_nhds
      (HeightLift.projection_isLocalHomeomorph R.hC).apply_self_mem_localInverseAt_source
  filter_upwards [hband, hsource, finite_parameter_chart_germ w] with z hz hzs hparam
  obtain ⟨hn, hparam⟩ := hparam
  have hproj : HeightLift.projection (R.lowerParameterLift q w z) =
      parameterSeamReflection h.out (finiteParameter ⟨z,hn⟩) := by
    change HeightLift.projection (l (parameterSeamReflection h.out (b.symm z))) = _
    rw [(HeightLift.projection_isLocalHomeomorph R.hC).apply_localInverseAt_of_mem hzs]
    rw [show b.symm z = finiteParameter ⟨z,hn⟩ from hparam]
  apply R.lowerSeamBand_glue_formula f j (R.lowerParameterLift q w z) ⟨z,hn⟩ hz
  rw [hproj, parameterSeamReflection_involutive]

end PaperHalfPeriodRealization
end KsIndex.KarcherData
