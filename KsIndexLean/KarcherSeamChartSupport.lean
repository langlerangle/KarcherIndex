module

public import KsIndexLean.KarcherSeamPairInjectivity

@[expose] public section


/-! The actual local seam parametrizations land in the two adjacent copies.
This uses the seam formula on a membership-detecting function, so the same
local lifting theorem controls both coordinates and their supporting copies. -/
noncomputable section
open Set Topology
open scoped Topology Classical KsIndex.KarcherData.ParameterAtlas
namespace KsIndex.KarcherData
namespace PaperHalfPeriodRealization
variable {k m : ℕ} [h : Fact (2 ≤ k)] [NeZero m] (R : PaperHalfPeriodRealization k)

def closedSeamPair (n : ZMod (2*m)) :=
  Set.range (R.orderedDiskPoint n) ∪ Set.range (R.orderedDiskPoint (n+1))

private def outsidePair (n : ZMod (2*m))
    (q : HeightLift.PeriodQuotient (extendedEWMap h.out (reflectionBasepoint k) R.C) m) : ℂ :=
  if q ∈ R.closedSeamPair n then 0 else 1

private lemma outsidePair_glue_zero (n : ZMod (2*m)) {z : ℂ}
    (hz : z ∉ Surface.punctures k) :
    Surface.glue (encodeDiskFunction (R.diskFunctionPullback (R.outsidePair n))) n z = 0 := by
  change (if ‖z‖ ≤ 1 then _ else _) = _
  split_ifs with hn
  · let w : PuncturedClosedDisk k := ⟨⟨z,hz⟩,hn⟩
    have he := encodeDiskFunction_on_disk (R.diskFunctionPullback (R.outsidePair n)) n w
    refine he.trans ?_
    change R.outsidePair n (R.orderedDiskPoint n w) = 0
    exact ite_eq_left (Or.inl ⟨w,rfl⟩)
  · have hgt : 1 < ‖z‖ := lt_of_not_ge hn
    have hs : ‖Bracket.σ z‖ ≤ 1 := by
      rw [Bracket.norm_σ]
      exact ((inv_lt_one₀ (lt_trans zero_lt_one hgt)).mpr hgt).le
    have hp : Bracket.σ z ∉ Surface.punctures k := by
      simpa only [Bracket.σ, one_div] using inverse_conjugate_not_puncture hz
    let w : PuncturedClosedDisk k := ⟨⟨Bracket.σ z,hp⟩,hs⟩
    have he := encodeDiskFunction_on_disk (R.diskFunctionPullback (R.outsidePair n)) (n+1) w
    refine he.trans ?_
    change R.outsidePair n (R.orderedDiskPoint (n+1) w) = 0
    exact ite_eq_left (Or.inr ⟨w,rfl⟩)

private lemma outsidePair_glue_zero_germ (n : ZMod (2*m)) (w : PuncturedPlane k) :
    Surface.glue (encodeDiskFunction (R.diskFunctionPullback (R.outsidePair n))) n
      =ᶠ[𝓝 w.val] (fun _ => 0) := by
  have hc : IsClosed (Surface.punctures k) :=
    isClosed_eq (continuous_id.pow (2*k)) continuous_const
  filter_upwards [hc.isOpen_compl.mem_nhds w.property] with z hz
  exact R.outsidePair_glue_zero n hz

lemma upperSeam_closedPair_germ (j : ℤ)
    (q : PeriodicEWCarrier h.out (reflectionBasepoint k) R.C) (w : PuncturedPlane k)
    (hq : q ∈ R.upperSeamBand j) (hp : HeightLift.projection q = finiteParameter w) :
    ∀ᶠ z in 𝓝 w.val,
      (HeightLift.periodChart R.hC m (HeightLift.periodQuotientMap m q)).symm z ∈
        R.closedSeamPair (evenCopyIndex (j : ZMod m)) := by
  have he := (R.upperSeam_glue_germ (R.outsidePair (evenCopyIndex (j : ZMod m))) j q w hq hp).trans
    (R.outsidePair_glue_zero_germ _ w)
  filter_upwards [he] with z hz
  by_contra hn
  have hz' : R.outsidePair (evenCopyIndex (j : ZMod m))
      ((HeightLift.periodChart R.hC m (HeightLift.periodQuotientMap m q)).symm z) = 0 := hz
  simp only [outsidePair, ite_eq_right hn] at hz'
  exact one_ne_zero hz'

lemma lowerSeam_closedPair_germ (j : ℤ)
    (q : PeriodicEWCarrier h.out (reflectionBasepoint k) R.C) (w : PuncturedPlane k)
    (hq : q ∈ R.lowerSeamBand j)
    (hp : parameterSeamReflection h.out (HeightLift.projection q) = finiteParameter w) :
    ∀ᶠ z in 𝓝 w.val,
      HeightLift.periodQuotientMap m (R.lowerParameterLift q w z) ∈
        R.closedSeamPair (oddCopyIndex (j : ZMod m)) := by
  have he := (R.lowerSeam_glue_germ (R.outsidePair (oddCopyIndex (j : ZMod m))) j q w hq hp).trans
    (R.outsidePair_glue_zero_germ _ w)
  filter_upwards [he] with z hz
  by_contra hn
  have hz' : R.outsidePair (oddCopyIndex (j : ZMod m))
      (HeightLift.periodQuotientMap m (R.lowerParameterLift q w z)) = 0 := hz
  simp only [outsidePair, ite_eq_right hn] at hz'
  exact one_ne_zero hz'

lemma closedSeamPair_mem_interiors {n : ZMod (2*m)}
    {q : HeightLift.PeriodQuotient (extendedEWMap h.out (reflectionBasepoint k) R.C) m}
    (hq : q ∈ R.closedSeamPair n) (hc : ‖R.seamPairCoordinate n q‖ ≠ 1) :
    q ∈ R.quotientCopyInterior n ∪ R.quotientCopyInterior (n+1) := by
  rcases hq with ⟨w,rfl⟩ | ⟨w,rfl⟩
  · rw [R.seamPairCoordinate_first] at hc
    exact Or.inl ⟨w, lt_of_le_of_ne w.property hc, rfl⟩
  · rw [R.seamPairCoordinate_second (copyIndex_ne_successor n), Bracket.norm_σ] at hc
    have hw : ‖w.val.val‖ ≠ 1 := fun hw => hc (by rw [hw, inv_one])
    exact Or.inr ⟨w, lt_of_le_of_ne w.property hw, rfl⟩

lemma seamPairCoordinate_unique {n : ZMod (2*m)}
    {x y : HeightLift.PeriodQuotient (extendedEWMap h.out (reflectionBasepoint k) R.C) m}
    {z : ℂ} (hy : y ∈ R.closedSeamPair n)
    (hx : x ∈ R.quotientCopyInterior n ∪ R.quotientCopyInterior (n+1))
    (hcy : R.seamPairCoordinate n y = z) (hcx : R.seamPairCoordinate n x = z)
    (hz0 : z ≠ 0) (hz1 : ‖z‖ ≠ 1) : y = x := by
  apply R.seamPairCoordinate_injOn (copyIndex_ne_successor n)
  · exact ⟨R.closedSeamPair_mem_interiors hy (by rw [hcy]; exact hz1),
      by change R.seamPairCoordinate n y ≠ 0; rw [hcy]; exact hz0⟩
  · exact ⟨hx, by change R.seamPairCoordinate n x ≠ 0; rw [hcx]; exact hz0⟩
  · exact hcy.trans hcx.symm

/-- The actual inverse chart recovers every point of the pair over a nearby
nonexceptional coordinate, not merely one chosen right inverse. -/
lemma upperSeam_pair_inverse_germ (j : ℤ)
    (q : PeriodicEWCarrier h.out (reflectionBasepoint k) R.C) (w : PuncturedPlane k)
    (hq : q ∈ R.upperSeamBand j) (hp : HeightLift.projection q = finiteParameter w) :
    ∀ᶠ z in 𝓝 w.val, ∀ x,
      x ∈ R.quotientCopyInterior (evenCopyIndex (j : ZMod m)) ∪
        R.quotientCopyInterior (evenCopyIndex (j : ZMod m) + 1) →
      R.seamPairCoordinate (evenCopyIndex (j : ZMod m)) x = z →
      z ≠ 0 → ‖z‖ ≠ 1 →
      (HeightLift.periodChart R.hC m (HeightLift.periodQuotientMap m q)).symm z = x := by
  filter_upwards [R.upperSeam_closedPair_germ (m := m) j q w hq hp,
    R.upperSeam_pairCoordinate_germ (m := m) j q w hq hp] with z hz hc
  intro x hx hcx hz0 hz1
  exact R.seamPairCoordinate_unique hz hx hc hcx hz0 hz1

lemma lowerSeam_pair_inverse_germ (j : ℤ)
    (q : PeriodicEWCarrier h.out (reflectionBasepoint k) R.C) (w : PuncturedPlane k)
    (hq : q ∈ R.lowerSeamBand j)
    (hp : parameterSeamReflection h.out (HeightLift.projection q) = finiteParameter w) :
    ∀ᶠ z in 𝓝 w.val, ∀ x,
      x ∈ R.quotientCopyInterior (oddCopyIndex (j : ZMod m)) ∪
        R.quotientCopyInterior (oddCopyIndex (j : ZMod m) + 1) →
      R.seamPairCoordinate (oddCopyIndex (j : ZMod m)) x = z →
      z ≠ 0 → ‖z‖ ≠ 1 →
      HeightLift.periodQuotientMap m (R.lowerParameterLift q w z) = x := by
  filter_upwards [R.lowerSeam_closedPair_germ (m := m) j q w hq hp,
    R.lowerSeam_pairCoordinate_germ (m := m) j q w hq hp] with z hz hc
  intro x hx hcx hz0 hz1
  exact R.seamPairCoordinate_unique hz hx hc hcx hz0 hz1

end PaperHalfPeriodRealization
end KsIndex.KarcherData
