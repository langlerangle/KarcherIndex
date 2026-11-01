module

public import KsIndexLean.KarcherDoubleSector

@[expose] public section


/-! Proper embedding of the two fundamental sectors joined along their common boundary. -/
noncomputable section
namespace KsIndex.KarcherData
open Set
namespace PaperHalfPeriodRealization
variable {k : ℕ} [h : Fact (2 ≤ k)]

def ambientYReflection : AmbientTriple ≃ₜ AmbientTriple :=
  (Homeomorph.refl ℝ).prodCongr ((Homeomorph.neg ℝ).prodCongr (Homeomorph.refl ℝ))

lemma continuous_centeredAmbient (R : PaperHalfPeriodRealization k) :
    Continuous (centeredLiftAmbient (k := k) R.C R.t) := by
  have ha := HeightLift.continuous_ambient R.hC
  exact (continuous_const.add ha.fst).prodMk
    (ha.snd.fst.prodMk (ha.snd.snd.add continuous_const))

/-- The two continuous sector parametrizations carry compact pieces into the
same intrinsic carrier, so properness survives their finite gluing. -/
lemma isProperMap_doubleSector (R : PaperHalfPeriodRealization k) :
    IsProperMap (fun q : R.doubleSector => centeredLiftAmbient R.C R.t q.val) := by
  apply isProperMap_iff_isCompact_preimage.mpr
  refine ⟨R.continuous_centeredAmbient.comp continuous_subtype_val, ?_⟩
  intro K hK
  have hA := R.isProperMap_heightStripImmersion.isCompact_preimage hK
  have hB := R.isProperMap_heightStripImmersion.isCompact_preimage
    (ambientYReflection.isCompact_preimage.mpr hK)
  have hc : Continuous (fun ζ => (R.heightStripPoint ζ).val) :=
    continuous_subtype_val.comp R.continuous_heightStripPoint
  have hleft := hA.image hc
  have hright := hB.image (R.continuous_conjugationLift.comp hc)
  apply Topology.IsEmbedding.subtypeVal.isCompact_iff.mpr
  convert hleft.union hright using 1
  ext q
  constructor
  · rintro ⟨⟨q, hq⟩, hKq, rfl⟩
    rcases hq with ⟨ζ, rfl⟩ | ⟨ζ, rfl⟩
    · exact Or.inl ⟨ζ, hKq, rfl⟩
    · right
      refine ⟨ζ, ?_, rfl⟩
      change ambientYReflection (R.heightStripImmersion ζ) ∈ K
      change centeredLiftAmbient R.C R.t (R.conjugationLift (R.heightStripPoint ζ).val) ∈ K at hKq
      rwa [R.conjugationLift_ambient] at hKq
  · rintro (⟨ζ, hζ, rfl⟩ | ⟨ζ, hζ, rfl⟩)
    · exact ⟨⟨(R.heightStripPoint ζ).val, Or.inl ⟨ζ, rfl⟩⟩, hζ, rfl⟩
    · refine ⟨⟨R.conjugationLift (R.heightStripPoint ζ).val, Or.inr ⟨ζ, rfl⟩⟩, ?_, rfl⟩
      change centeredLiftAmbient R.C R.t (R.conjugationLift (R.heightStripPoint ζ).val) ∈ K
      rw [R.conjugationLift_ambient]
      exact hζ

lemma isClosedEmbedding_doubleSector (R : PaperHalfPeriodRealization k) :
    Topology.IsClosedEmbedding
      (fun q : R.doubleSector => centeredLiftAmbient R.C R.t q.val) := by
  apply Topology.IsClosedEmbedding.of_continuous_injective_isClosedMap
    (R.continuous_centeredAmbient.comp continuous_subtype_val) _
    R.isProperMap_doubleSector.isClosedMap
  intro q p he
  exact Subtype.ext (R.doubleSector_injective q.property p.property he)

end PaperHalfPeriodRealization
end KsIndex.KarcherData
