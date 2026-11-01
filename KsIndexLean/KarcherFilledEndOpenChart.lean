module

public import KsIndexLean.KarcherFilledEndNeighborhood

@[expose] public section


/-! Open surface charts at the filled end vertices. -/
noncomputable section
open Set Topology Filter
namespace KsIndex.KarcherData.DiskCompactification
variable {k m : ℕ} [h : Fact (2 ≤ k)] [NeZero m]
variable (R : PaperHalfPeriodRealization k) {w : ℂ} (hw : w ∈ Surface.punctures k)

def puncturedEndInverse (t : quotientEndTarget h.out hw (reflectionBasepoint k) (m := m)) :
    FilledChain k m :=
  (periodQuotientHomeomorph R ((quotientEndHomeomorph h.out (NeZero.pos m) hw
    (reflectionBasepoint k) R.C R.hC).symm t).val).val

lemma puncturedEndInverse_isOpenMap : IsOpenMap (puncturedEndInverse R (m := m) hw) := by
  have hs : IsOpen (quotientEndSource h.out hw (reflectionBasepoint k) R.C (m := m)) := by
    rw [quotientEndSource_eq]
    exact (isOpen_endParameterRegion h.out hw).preimage
      (HeightLift.quotientProjection_isLocalHomeomorph R.hC m).continuous
  exact regularSet_isOpen.isOpenMap_subtype_val.comp
    ((periodQuotientHomeomorph R).isOpenMap.comp (hs.isOpenMap_subtype_val.comp
      (quotientEndHomeomorph h.out (NeZero.pos m) hw
        (reflectionBasepoint k) R.C R.hC).symm.isOpenMap))

lemma filledEndInverse_isOpenMap : IsOpenMap (filledEndInverse R (m := m) hw) := by
  classical
  intro U hU
  apply isOpen_iff_mem_nhds.mpr
  rintro q ⟨t, htU, rfl⟩
  by_cases ht : t.val = 0
  · have he : t = endCenter hw := Subtype.ext ht
    subst t
    rw [filledEndInverse_center]
    have hpre : U ∈ 𝓝 (endCenter (m := m) hw) := hU.mem_nhds htU
    obtain ⟨ε, hε, hsub⟩ := Metric.mem_nhds_iff.mp hpre
    obtain ⟨r, hr0, hr⟩ := exists_closedEndDisk (m := m) hw
    let s := min r (ε / 2)
    have hs0 : 0 < s := lt_min hr0 (half_pos hε)
    have hsr : Metric.closedBall (0 : ℂ) s ⊆ EndRegion (m := m) hw :=
      fun z hz => hr (Metric.closedBall_subset_closedBall (min_le_left _ _) hz)
    apply mem_of_superset (closedEndImage_mem_nhds R hw s hs0 hsr)
    rintro _ ⟨z, rfl⟩
    refine ⟨⟨z.val, hsr z.property⟩, ?_, rfl⟩
    apply hsub
    change dist z.val (0 : ℂ) < ε
    exact lt_of_le_of_lt z.property ((min_le_right _ _).trans_lt (half_lt_self hε))
  · let T := quotientEndTarget h.out hw (reflectionBasepoint k) (m := m)
    let g : T → EndRegion (m := m) hw := fun u => ⟨u.val, by
      have hh := congrArg (fun S : Set ℂ => u.val ∈ S)
        (quotientEndTarget_eq h.out (NeZero.pos m) hw (reflectionBasepoint k))
      exact (hh.mp u.property).1⟩
    have hg : Continuous g := by fun_prop
    let u : T := ⟨t.val, by
      change t.val ∈ quotientEndTarget h.out hw (reflectionBasepoint k) (m := m)
      rw [quotientEndTarget_eq h.out (NeZero.pos m) hw (reflectionBasepoint k)]
      exact ⟨t.property, ht⟩⟩
    have heq (v : T) : puncturedEndInverse R hw v = filledEndInverse R hw (g v) := by
      have hh := congrArg (fun S : Set ℂ => v.val ∈ S)
        (quotientEndTarget_eq h.out (NeZero.pos m) hw (reflectionBasepoint k))
      simp only [filledEndInverse, g, dite_eq_right (hh.mp v.property).2]
      rfl
    have ho := puncturedEndInverse_isOpenMap R hw (g ⁻¹' U) (hU.preimage hg)
    have hm : filledEndInverse R hw t ∈ puncturedEndInverse R hw '' (g ⁻¹' U) :=
      ⟨u, htU, heq u⟩
    apply mem_of_superset (ho.mem_nhds hm)
    rintro _ ⟨v, hv, rfl⟩
    exact ⟨g v, hv, (heq v).symm⟩

/-- The full root region, including zero, embeds as an open neighborhood in
the compactification. -/
theorem filledEndInverse_isOpenEmbedding :
    Topology.IsOpenEmbedding (filledEndInverse R (m := m) hw) :=
  .of_continuous_injective_isOpenMap (continuous_filledEndInverse R hw)
    (filledEndInverse_injective R hw) (filledEndInverse_isOpenMap R hw)

/-- An open neighborhood of the filled vertex is homeomorphic to the open
complex root region, with zero corresponding to that vertex. -/
def filledEndHomeomorph : EndRegion (m := m) hw ≃ₜ Set.range (filledEndInverse R (m := m) hw) :=
  (filledEndInverse_isOpenEmbedding R hw).isEmbedding.toHomeomorph

local instance : Nonempty (EndRegion (m := m) hw) := ⟨endCenter hw⟩

/-- A complex topological chart at the filled endpoint. -/
def filledVertexChart : OpenPartialHomeomorph (FilledChain k m) ℂ :=
  ((filledEndInverse_isOpenEmbedding R hw).toOpenPartialHomeomorph
    (filledEndInverse R hw)).symm.trans
      (Topology.IsOpenEmbedding.toOpenPartialHomeomorph
        (fun t : EndRegion (m := m) hw => t.val)
        (isOpen_filledEndRootRegion h.out hw (reflectionBasepoint k)).isOpenEmbedding_subtypeVal)

lemma filledVertexChart_source : (filledVertexChart R (m := m) hw).source =
    Set.range (filledEndInverse R hw) := by
  simp only [filledVertexChart, OpenPartialHomeomorph.trans_source,
    OpenPartialHomeomorph.symm_source,
    Topology.IsOpenEmbedding.toOpenPartialHomeomorph_source,
    Topology.IsOpenEmbedding.toOpenPartialHomeomorph_target,
    Set.preimage_univ, Set.inter_univ]

lemma vertex_mem_filledVertexChart : vertex w hw ∈ (filledVertexChart R (m := m) hw).source := by
  rw [filledVertexChart_source]
  exact ⟨endCenter hw, filledEndInverse_center R hw⟩

lemma filledVertexChart_vertex : filledVertexChart R (m := m) hw (vertex w hw) = 0 := by
  rw [← filledEndInverse_center R hw]
  simp only [filledVertexChart, OpenPartialHomeomorph.trans_apply,
    Topology.IsOpenEmbedding.toOpenPartialHomeomorph_left_inv,
    Topology.IsOpenEmbedding.toOpenPartialHomeomorph_apply]
  rfl

end KsIndex.KarcherData.DiskCompactification
