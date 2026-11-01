module

public import KsIndexLean.KarcherLiftCharts

@[expose] public section


/-! Local topology of the genuine period quotient projection. -/
noncomputable section
open Set Topology
namespace KsIndex.KarcherData.HeightLift
variable {P : Type*} [TopologicalSpace P] {F : P → PeriodTarget}

def periodQuotientMap (m : ℕ) : HeightLift F → PeriodQuotient F m := Quotient.mk _

lemma periodQuotientMap_isQuotientMap (m : ℕ) :
    IsQuotientMap (periodQuotientMap (F := F) m) := isQuotientMap_quotient_mk'

lemma periodQuotientMap_isOpenMap (m : ℕ) :
    IsOpenMap (periodQuotientMap (F := F) m) := by
  intro U hU
  apply (periodQuotientMap_isQuotientMap (F := F) m).isOpen_preimage.mp
  have he : periodQuotientMap m ⁻¹' (periodQuotientMap (F := F) m '' U) =
      ⋃ n : ℤ, deck (n * (m : ℤ)) '' U := by
    ext q
    constructor
    · rintro ⟨r, hr, he⟩
      obtain ⟨n, hn⟩ := Quotient.exact he
      exact mem_iUnion.mpr ⟨n, r, hr, hn⟩
    · intro hq
      obtain ⟨n, r, hr, rfl⟩ := mem_iUnion.mp hq
      exact ⟨r, hr, Quotient.sound ⟨n, rfl⟩⟩
  rw [he]
  exact isOpen_iUnion (fun n => (deckHomeomorph (n * (m : ℤ))).isOpenMap U hU)

lemma periodQuotientMap_strip_injective (hF : Continuous F) (m : ℕ) (a : ℝ) :
    Function.Injective (fun q : strip (F := F) a => periodQuotientMap m q.val) := by
  intro q r he
  apply (stripHomeomorph hF a).injective
  apply Subtype.ext
  have hp := congrArg (quotientProjection (F := F) m) he
  exact hp

/-- Each open height strip is an actual quotient chart. -/
lemma periodQuotientMap_strip_isOpenEmbedding (hF : Continuous F) (m : ℕ) (a : ℝ) :
    IsOpenEmbedding (fun q : strip (F := F) a => periodQuotientMap m q.val) := by
  apply isOpenEmbedding_iff_continuous_injective_isOpenMap.mpr
  exact ⟨(periodQuotientMap_isQuotientMap m).continuous.comp continuous_subtype_val,
    periodQuotientMap_strip_injective hF m a,
    (periodQuotientMap_isOpenMap m).comp (isOpen_strip a).isOpenEmbedding_subtypeVal.isOpenMap⟩

lemma periodQuotientMap_isLocalHomeomorph (hF : Continuous F) (m : ℕ) :
    IsLocalHomeomorph (periodQuotientMap (F := F) m) := by
  apply isLocalHomeomorph_iff_isOpenEmbedding_restrict.mpr
  intro q
  exact ⟨strip (height q - Real.pi), (isOpen_strip _).mem_nhds (mem_centered_strip q),
    periodQuotientMap_strip_isOpenEmbedding hF m _⟩

/-- The quotient retains local parameter charts, rather than merely a set projection. -/
lemma quotientProjection_isLocalHomeomorph (hF : Continuous F) (m : ℕ) :
    IsLocalHomeomorph (quotientProjection (F := F) m) := by
  have hc : IsLocalHomeomorphOn
      (quotientProjection m ∘ periodQuotientMap (F := F) m) Set.univ :=
    (projection_isLocalHomeomorph hF).isLocalHomeomorphOn
  have ht := hc.of_comp_right (periodQuotientMap_isLocalHomeomorph hF m).isLocalHomeomorphOn
  rw [Set.image_univ, (periodQuotientMap_isQuotientMap m).surjective.range_eq] at ht
  exact isLocalHomeomorph_iff_isLocalHomeomorphOn_univ.mpr ht

end KsIndex.KarcherData.HeightLift
