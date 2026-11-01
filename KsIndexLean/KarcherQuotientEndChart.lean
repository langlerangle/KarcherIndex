module

public import KsIndexLean.KarcherEndRootTopology

@[expose] public section


/-! The signed root gives a homeomorphism from the actual quotient end region
to the corresponding complex root region. -/
noncomputable section
namespace KsIndex.KarcherData

variable {k m : ℕ} (hk : 2 ≤ k) (hm : 0 < m) {w : ℂ}
  (hw : w ∈ Surface.punctures k) (b : PuncturedPlane k) (C : PeriodTarget)

def quotientEndSource : Set (HeightLift.PeriodQuotient (extendedEWMap hk b C) m) :=
  {x | ∃ z : PuncturedPlane k, z.val ∈ (endCoordinateChart hk hw).source ∧
    HeightLift.quotientProjection m x = finiteParameter z}

def quotientEndTarget : Set ℂ :=
  {t | ∃ z : PuncturedPlane k, z.val ∈ (endCoordinateChart hk hw).source ∧
    t ^ m = endCoordinate k w z.val / endCoordinate k w b.val}

lemma quotientEndSource_eq : quotientEndSource hk hw b C (m := m) =
    HeightLift.quotientProjection m ⁻¹' endParameterRegion hk hw := by
  ext x
  constructor
  · rintro ⟨z, hz, he⟩
    exact ⟨z, hz, he.symm⟩
  · rintro ⟨z, hz, he⟩
    exact ⟨z, hz, he.symm⟩

lemma quotientEndRoot_bijOn_source : Set.BijOn (quotientEndRoot hk hm b w C)
    (quotientEndSource hk hw b C) (quotientEndTarget hk hw b (m := m)) := by
  apply quotientEndRoot_bijOn hk hm b w C
  intro z hz v hv he
  apply Subtype.ext
  apply (endCoordinateChart hk hw).injOn hz hv
  change endCoordinate k w z.val = endCoordinate k w v.val
  exact (div_left_inj' (endCoordinate_ne_zero_at_finite w b)).mp he

/-- On the entire quotient preimage, all sheets together form an open
embedded complex root region. -/
theorem quotientEndRoot_source_isOpenEmbedding
    (hF : Continuous (extendedEWMap hk b C)) :
    Topology.IsOpenEmbedding (fun x : quotientEndSource hk hw b C =>
      quotientEndRoot hk hm b w C x.val) := by
  have hs : IsOpen (quotientEndSource hk hw b C (m := m)) := by
    rw [quotientEndSource_eq]
    exact (isOpen_endParameterRegion hk hw).preimage
      (HeightLift.quotientProjection_isLocalHomeomorph hF m).continuous
  have hf : IsLocalHomeomorphOn (quotientEndRoot hk hm b w C)
      (quotientEndSource hk hw b C) := by
    rw [quotientEndSource_eq]
    exact quotientEndRoot_isLocalHomeomorphOn hk hm hw b C hF
  have hlocal : IsLocalHomeomorph (fun x : quotientEndSource hk hw b C =>
      quotientEndRoot hk hm b w C x.val) := by
    apply isLocalHomeomorph_iff_isLocalHomeomorphOn_univ.mpr
    exact hf.comp hs.isOpenEmbedding_subtypeVal.isLocalHomeomorph.isLocalHomeomorphOn
      (fun x _ => x.property)
  apply hlocal.isOpenEmbedding_of_injective
  intro x y he
  apply Subtype.ext
  exact (quotientEndRoot_bijOn_source hk hm hw b C).injOn x.property y.property he

lemma quotientEndRoot_source_range :
    Set.range (fun x : quotientEndSource hk hw b C => quotientEndRoot hk hm b w C x.val) =
      quotientEndTarget hk hw b (m := m) := by
  ext t
  constructor
  · rintro ⟨x, rfl⟩
    exact (quotientEndRoot_bijOn_source hk hm hw b C).mapsTo x.property
  · intro ht
    obtain ⟨x, hx, he⟩ := (quotientEndRoot_bijOn_source hk hm hw b C).surjOn ht
    exact ⟨⟨x, hx⟩, he⟩

/-- The concrete quotient end-chart homeomorphism, with no abstract
replacement of the EW carrier. -/
def quotientEndHomeomorph (hF : Continuous (extendedEWMap hk b C)) :
    quotientEndSource hk hw b C (m := m) ≃ₜ quotientEndTarget hk hw b (m := m) :=
  (quotientEndRoot_source_isOpenEmbedding hk hm hw b C hF).isEmbedding.toHomeomorph.trans
    (Homeomorph.setCongr (quotientEndRoot_source_range hk hm hw b C))

@[simp] theorem quotientEndHomeomorph_apply (hF : Continuous (extendedEWMap hk b C))
    (x : quotientEndSource hk hw b C (m := m)) :
    (quotientEndHomeomorph hk hm hw b C hF x).val = quotientEndRoot hk hm b w C x.val := rfl

end KsIndex.KarcherData
