module

public import KsIndexLean.KarcherHeightStripEmbedding
public import KsIndexLean.KarcherHeightSectorCorrespondence
public import KsIndexLean.KarcherSectorInjectivity
public import KsIndexLean.KarcherHalfPeriodHomeomorph

@[expose] public section


/-! A proper embedding of a closed fundamental sector by the actual normalized
EW immersion, including its finite boundary and with its end puncture omitted. -/
noncomputable section
namespace KsIndex.KarcherData
open Complex Set
namespace PaperHalfPeriodRealization
variable {k : ℕ} [h : Fact (2 ≤ k)]

/-- The actual intrinsic half-period point corresponding to a strip parameter. -/
def heightStripPoint (R : PaperHalfPeriodRealization k) (ζ : HeightStrip) :
    PaperHalfPeriod h.out (reflectionBasepoint k) R.C :=
  R.diskHomeomorph.symm
    ⟨⟨heightSectorParameter k ζ.val,
      heightStrip_parameter_not_puncture (by have := h.out; omega) ζ.property⟩,
      heightStrip_parameter_norm (by have := h.out; omega) ζ.property⟩

lemma heightStripPoint_projection (R : PaperHalfPeriodRealization k) (ζ : HeightStrip) :
    HeightLift.projection (R.heightStripPoint ζ).val = finiteParameter
      ⟨heightSectorParameter k ζ.val,
        heightStrip_parameter_not_puncture (by have := h.out; omega) ζ.property⟩ :=
  R.diskHomeomorph_symm_projection _

lemma continuous_heightStripPoint (R : PaperHalfPeriodRealization k) :
    Continuous R.heightStripPoint := by
  apply R.diskHomeomorph.symm.continuous.comp
  apply Continuous.subtype_mk
  apply Continuous.subtype_mk
  apply continuous_iff_continuousAt.mpr
  intro ζ
  exact (continuousAt_heightSectorParameter (by have := h.out; omega : k ≠ 0)
    ζ.property).comp (f := fun ζ : HeightStrip => ζ.val) continuous_subtype_val.continuousAt

/-- The sector's parametrization uses the already constructed EW carrier and map. -/
def heightStripImmersion (R : PaperHalfPeriodRealization k) (ζ : HeightStrip) : AmbientTriple :=
  centeredLiftAmbient R.C R.t (R.heightStripPoint ζ).val

lemma heightStripImmersion_yz (R : PaperHalfPeriodRealization k) (ζ : HeightStrip) :
    ((R.heightStripImmersion ζ).2.1, (R.heightStripImmersion ζ).2.2 - Real.pi / 2) =
      heightStripYZ h.out (reflectionBasepoint k) ζ := by
  have hh := R.heightStrip_actual_height ζ.property (R.heightStripPoint ζ).val
    (R.heightStripPoint_projection ζ) (R.heightStripPoint ζ).property
  have hy := (centeredLiftAmbient_horiz_descended R (R.heightStripPoint ζ).val _
    (R.heightStripPoint_projection ζ)).2
  apply Prod.ext
  · change _ = horizontalY h.out (reflectionBasepoint k) (heightSectorParameter k ζ.val)
    simp only [horizontalY, heightStrip_parameter_not_puncture
      (by have := h.out; omega : k ≠ 0) ζ.property]
    exact hy
  · change (centeredLiftAmbient R.C R.t (R.heightStripPoint ζ).val).2.2 - Real.pi / 2 = ζ.val.im
    linarith

lemma continuous_heightStripImmersion (R : PaperHalfPeriodRealization k) :
    Continuous R.heightStripImmersion := by
  have hq := continuous_subtype_val.comp R.continuous_heightStripPoint
  have ha := (HeightLift.continuous_ambient R.hC).comp hq
  exact (continuous_const.add ha.fst).prodMk
    (ha.snd.fst.prodMk (ha.snd.snd.add continuous_const))

/-- Properness of the actual sector immersion follows from the uniform end escape. -/
lemma isProperMap_heightStripImmersion (R : PaperHalfPeriodRealization k) :
    IsProperMap R.heightStripImmersion := by
  let g : AmbientTriple → ℝ × ℝ := fun v => (v.2.1, v.2.2 - Real.pi / 2)
  apply isProperMap_of_comp_of_t2 R.continuous_heightStripImmersion
    (show Continuous g by fun_prop)
  have he : g ∘ R.heightStripImmersion = heightStripYZ h.out (reflectionBasepoint k) :=
    funext (R.heightStripImmersion_yz)
  rw [he]
  exact isProperMap_heightStripYZ h.out (reflectionBasepoint k)

/-- The actual normalized EW immersion embeds the closed fundamental sector. -/
lemma isClosedEmbedding_heightStripImmersion (R : PaperHalfPeriodRealization k) :
    Topology.IsClosedEmbedding R.heightStripImmersion := by
  apply Topology.IsClosedEmbedding.of_continuous_injective_isClosedMap
    R.continuous_heightStripImmersion _ R.isProperMap_heightStripImmersion.isClosedMap
  intro ζ ξ he
  apply (isClosedEmbedding_heightStripYZ h.out (reflectionBasepoint k)).injective
  rw [← R.heightStripImmersion_yz ζ, ← R.heightStripImmersion_yz ξ, he]

end PaperHalfPeriodRealization
end KsIndex.KarcherData
