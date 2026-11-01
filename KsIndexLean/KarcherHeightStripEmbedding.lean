module

public import KsIndexLean.KarcherHeightStripEscape
public import Mathlib.Topology.Maps.Proper.CompactlyGenerated

@[expose] public section


/-! A proper topological embedding of the logarithmic sector by its horizontal
coordinate and height. -/
noncomputable section
namespace KsIndex.KarcherData
open Complex Set

abbrev HeightStrip := {ζ : ℂ // heightStrip ζ}

def heightStripYZ {k : ℕ} (hk : 2 ≤ k) (b : PuncturedPlane k) (ζ : HeightStrip) : ℝ × ℝ :=
  (horizontalY hk b (heightSectorParameter k ζ.val), ζ.val.im)

lemma isClosed_heightStrip : IsClosed {ζ : ℂ | heightStrip ζ} :=
  (isClosed_le Complex.continuous_re continuous_const).inter
    ((isClosed_le continuous_const Complex.continuous_im).inter
      (isClosed_le Complex.continuous_im continuous_const))

lemma continuous_heightStripYZ {k : ℕ} (hk : 2 ≤ k) (b : PuncturedPlane k) :
    Continuous (heightStripYZ hk b) := by
  exact (heightStrip_horizontal_continuousOn hk b).domRestrict.prodMk
    (Complex.continuous_im.comp continuous_subtype_val)

/-- Bounded ambient position cannot accumulate at the omitted puncture. -/
lemma isProperMap_heightStripYZ {k : ℕ} (hk : 2 ≤ k) (b : PuncturedPlane k) :
    IsProperMap (heightStripYZ hk b) := by
  apply isProperMap_iff_isCompact_preimage.mpr
  refine ⟨continuous_heightStripYZ hk b, ?_⟩
  intro K hK
  obtain ⟨L, hL⟩ := (hK.image continuous_fst).bddBelow
  obtain ⟨S, hS⟩ := heightStrip_bounded_position_bounds_radius hk b L
  apply Topology.IsEmbedding.subtypeVal.isCompact_iff.mpr
  apply (isCompact_Icc.reProdIm (isCompact_Icc (a := 0) (b := Real.pi / 2))).of_isClosed_subset
  · exact isClosed_heightStrip.isClosedEmbedding_subtypeVal.isClosedMap _
      (hK.isClosed.preimage (continuous_heightStripYZ hk b))
  · rintro ζ ⟨q, hq, rfl⟩
    change q.val.re ∈ Icc S 0 ∧ q.val.im ∈ Icc 0 (Real.pi / 2)
    refine ⟨⟨hS q.val q.property ?_, q.property.1⟩, q.property.2⟩
    exact hL ⟨heightStripYZ hk b q, hq, rfl⟩

/-- The coordinate pair is a genuine embedding, not merely an injective immersion. -/
lemma isClosedEmbedding_heightStripYZ {k : ℕ} (hk : 2 ≤ k) (b : PuncturedPlane k) :
    Topology.IsClosedEmbedding (heightStripYZ hk b) := by
  apply Topology.IsClosedEmbedding.of_continuous_injective_isClosedMap
    (continuous_heightStripYZ hk b) _ (isProperMap_heightStripYZ hk b).isClosedMap
  intro ζ ξ he
  apply Subtype.ext
  exact heightStrip_Y_im_injective hk b ζ.property ξ.property he

end KsIndex.KarcherData
