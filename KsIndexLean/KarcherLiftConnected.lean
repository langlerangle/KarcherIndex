module

public import KsIndexLean.KarcherChainLift

@[expose] public section


/-! Path connectedness of the actual periodic EW lift. -/
noncomputable section
open Set Topology
open scoped KsIndex.KarcherData.ParameterAtlas
namespace KsIndex.KarcherData

/-- Finite lifts are dense, since their projection is open and finite parameters
 are dense in the sphere. -/
lemma dense_finite_lifts {k : ℕ} [h : Fact (2 ≤ k)] (base : PuncturedPlane k)
    (C : PeriodTarget) (hC : Continuous (extendedEWMap h.out base C)) :
    Dense ((HeightLift.projection (F := extendedEWMap h.out base C)) ⁻¹'
      Set.range (finiteParameter (k := k))) :=
  (denseRange_finiteParameter (k := k)).preimage
    (HeightLift.projection_isLocalHomeomorph hC).isOpenMap

/-- Every point, including points above infinity, can be joined to a finite lift.
 This uses local path connectedness of the established atlas, not asymptotics. -/
theorem joined_to_finite_lift {k : ℕ} [h : Fact (2 ≤ k)] (base : PuncturedPlane k)
    (C : PeriodTarget) (hC : Continuous (extendedEWMap h.out base C))
    (q : PeriodicEWCarrier h.out base C) :
    ∃ r : PeriodicEWCarrier h.out base C, ∃ w : PuncturedPlane k,
      HeightLift.projection r = finiteParameter w ∧ Joined q r := by
  let := HeightLift.liftChartedSpace hC
  let : LocallyPathConnectedSpace (PeriodicEWCarrier h.out base C) :=
    ChartedSpace.locallyPathConnectedSpace ℂ _
  obtain ⟨r, ⟨w, hw⟩, hr⟩ := (dense_finite_lifts base C hC).exists_mem_open
    (IsOpen.pathComponent q) ⟨q, mem_pathComponent_self q⟩
  exact ⟨r, w, hw.symm, hr⟩

/-- The actual integral periods connect all sheets, and local charts attach
 infinity: the intrinsic periodic EW surface is path connected. -/
theorem periodicEW_pathConnected {k : ℕ} [h : Fact (2 ≤ k)] (base : PuncturedPlane k)
    (C : PeriodTarget) (hC : Continuous (extendedEWMap h.out base C)) :
    PathConnectedSpace (PeriodicEWCarrier h.out base C) where
  nonempty := by
    obtain ⟨q, _⟩ := HeightLift.projection_surjective (F := extendedEWMap h.out base C)
      (finiteParameter base)
    exact ⟨q⟩
  joined q r := by
    obtain ⟨q', b, hb, hq⟩ := joined_to_finite_lift base C hC q
    obtain ⟨r', w, hw, hr⟩ := joined_to_finite_lift base C hC r
    exact hq.trans ((joined_finite_lifts h.out base b w C q' r' hb hw).trans hr.symm)

/-- Connectedness is attained by the actual continuous EW extension. -/
theorem exists_pathConnected_periodicEW {k : ℕ} [h : Fact (2 ≤ k)] (base : PuncturedPlane k) :
    ∃ C : PeriodTarget, Continuous (extendedEWMap h.out base C) ∧
      PathConnectedSpace (PeriodicEWCarrier h.out base C) := by
  obtain ⟨C, hC, _⟩ := exists_continuous_extendedEWMap h.out base
  exact ⟨C, hC, periodicEW_pathConnected base C hC⟩

end KsIndex.KarcherData
