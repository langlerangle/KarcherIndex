module

public import KsIndexLean.KarcherSeamPairArea
public import KsIndexLean.KarcherLowerSeamGerm

@[expose] public section


/-! The unfolded disk-pair coordinates agree locally with the actual quotient
atlas at upper seams, and with the reflected parameter lift at lower seams. -/
noncomputable section
open Set Topology
open scoped Topology KsIndex.KarcherData.ParameterAtlas
namespace KsIndex.KarcherData
namespace PaperHalfPeriodRealization
variable {k m : ℕ} [h : Fact (2 ≤ k)] [NeZero m] (R : PaperHalfPeriodRealization k)

lemma copyIndex_ne_successor (n : ZMod (2*m)) : n ≠ n + 1 := by
  let : Fact (1 < 2*m) := ⟨by have := NeZero.ne m; omega⟩
  intro he
  have hh : n + 0 = n + 1 := by simpa only [add_zero] using he
  exact zero_ne_one (add_left_cancel hh)

lemma seamPairCoordinate_glue (n : ZMod (2*m)) {z : ℂ}
    (hz : z ∉ Surface.punctures k) :
    Surface.glue (encodeDiskFunction (R.diskFunctionPullback (R.seamPairCoordinate n))) n z = z := by
  change (if ‖z‖ ≤ 1 then _ else _) = _
  split_ifs with hn
  · let w : PuncturedClosedDisk k := ⟨⟨z, hz⟩, hn⟩
    have he := encodeDiskFunction_on_disk
      (R.diskFunctionPullback (R.seamPairCoordinate n)) n w
    exact he.trans (R.seamPairCoordinate_first n w)
  · have hgt : 1 < ‖z‖ := lt_of_not_ge hn
    have hs : ‖Bracket.σ z‖ ≤ 1 := by
      rw [Bracket.norm_σ]
      exact ((inv_lt_one₀ (lt_trans zero_lt_one hgt)).mpr hgt).le
    have hp : Bracket.σ z ∉ Surface.punctures k := by
      simpa only [Bracket.σ, one_div] using inverse_conjugate_not_puncture hz
    let w : PuncturedClosedDisk k := ⟨⟨Bracket.σ z, hp⟩, hs⟩
    have he := encodeDiskFunction_on_disk
      (R.diskFunctionPullback (R.seamPairCoordinate n)) (n+1) w
    exact he.trans ((R.seamPairCoordinate_second (copyIndex_ne_successor n) w).trans
      (Bracket.σ_σ z))

lemma seamPairCoordinate_glue_germ (n : ZMod (2*m)) (w : PuncturedPlane k) :
    Surface.glue (encodeDiskFunction (R.diskFunctionPullback (R.seamPairCoordinate n))) n
      =ᶠ[𝓝 w.val] (fun z => z) := by
  have hc : IsClosed (Surface.punctures k) :=
    isClosed_eq (continuous_id.pow (2*k)) continuous_const
  filter_upwards [hc.isOpen_compl.mem_nhds w.property] with z hz
  exact R.seamPairCoordinate_glue n hz

lemma upperSeam_pairCoordinate_germ (j : ℤ)
    (q : PeriodicEWCarrier h.out (reflectionBasepoint k) R.C) (w : PuncturedPlane k)
    (hq : q ∈ R.upperSeamBand j) (hp : HeightLift.projection q = finiteParameter w) :
    (R.seamPairCoordinate (evenCopyIndex (j : ZMod m)) ∘
      (HeightLift.periodChart R.hC m (HeightLift.periodQuotientMap m q)).symm)
      =ᶠ[𝓝 w.val] (fun z => z) :=
  (R.upperSeam_glue_germ _ j q w hq hp).trans (R.seamPairCoordinate_glue_germ _ w)

lemma lowerSeam_pairCoordinate_germ (j : ℤ)
    (q : PeriodicEWCarrier h.out (reflectionBasepoint k) R.C) (w : PuncturedPlane k)
    (hq : q ∈ R.lowerSeamBand j)
    (hp : parameterSeamReflection h.out (HeightLift.projection q) = finiteParameter w) :
    (fun z => R.seamPairCoordinate (oddCopyIndex (j : ZMod m))
      (HeightLift.periodQuotientMap m (R.lowerParameterLift q w z)))
      =ᶠ[𝓝 w.val] (fun z => z) :=
  (R.lowerSeam_glue_germ _ j q w hq hp).trans (R.seamPairCoordinate_glue_germ _ w)

end PaperHalfPeriodRealization
end KsIndex.KarcherData
