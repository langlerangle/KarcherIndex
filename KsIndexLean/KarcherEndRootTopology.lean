module

public import KsIndexLean.KarcherEndProjectionTopology
public import KsIndexLean.ComplexRootChart

@[expose] public section


/-! Local topology of the actual signed quotient end root. -/
noncomputable section
namespace KsIndex.KarcherData

private lemma localHomeomorphOn_congr_open {X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] {f g : X → Y} {s : Set X} (hs : IsOpen s)
    (hf : IsLocalHomeomorphOn f s) (heq : Set.EqOn g f s) :
    IsLocalHomeomorphOn g s := by
  apply IsLocalHomeomorphOn.mk
  intro x hx
  obtain ⟨e, he, hfe⟩ := hf x hx
  refine ⟨e.restr s, ?_, ?_⟩
  · exact ⟨he, by simpa only [hs.interior_eq] using hx⟩
  · intro y hy
    change g y = e y
    rw [heq (by simpa only [hs.interior_eq] using hy.2), hfe]

lemma isOpen_endParameterRegion {k : ℕ} (hk : 2 ≤ k) {w : ℂ}
    (hw : w ∈ Surface.punctures k) : IsOpen (endParameterRegion hk hw) :=
  (isOpenEmbedding_finiteParameter k).isOpenMap _
    ((endCoordinateChart hk hw).open_source.preimage continuous_subtype_val)

/-- On the actual quotient preimage of the base IFT neighborhood, the signed
root is locally a homeomorphism. -/
theorem quotientEndRoot_isLocalHomeomorphOn {k m : ℕ} (hk : 2 ≤ k) (hm : 0 < m)
    {w : ℂ} (hw : w ∈ Surface.punctures k) (b : PuncturedPlane k) (C : PeriodTarget)
    (hF : Continuous (extendedEWMap hk b C)) :
    IsLocalHomeomorphOn (quotientEndRoot hk hm b w C)
      (HeightLift.quotientProjection m ⁻¹' endParameterRegion hk hw) := by
  have hp := HeightLift.quotientProjection_isLocalHomeomorph hF m
  have hs : IsOpen (HeightLift.quotientProjection (F := extendedEWMap hk b C) m ⁻¹'
      endParameterRegion hk hw) := (isOpen_endParameterRegion hk hw).preimage hp.continuous
  apply KsIndex.isLocalHomeomorphOn_complex_root hm
  · intro x hx
    obtain ⟨z, hz, he⟩ := hx
    exact continuousAt_quotientEndRoot_finite hk hm b z w C x he.symm
  · intro x hx
    unfold quotientEndRoot
    split_ifs
    · exact parameterRoot_ne_zero hk hm b C x
    · exact inv_ne_zero (parameterRoot_ne_zero hk hm b C x)
  · apply localHomeomorphOn_congr_open hs
      (quotient_endCoordinate_isLocalHomeomorphOn hk hw b C hF)
    intro x hx
    obtain ⟨z, hz, he⟩ := hx
    change quotientEndRoot hk hm b w C x ^ m =
      parameterEndCoordinate b w (HeightLift.quotientProjection m x)
    rw [← he, parameterEndCoordinate_finite]
    exact quotientEndRoot_pow_finite hk hm b z w C x he.symm

end KsIndex.KarcherData
