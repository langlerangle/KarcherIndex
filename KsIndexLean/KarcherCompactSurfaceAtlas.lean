module

public import KsIndexLean.KarcherFilledEndOpenChart
public import KsIndexLean.KarcherPeriodQuotientManifold

@[expose] public section


/-! A complex topological atlas on the compactified EW quotient. -/
noncomputable section
open Set Topology
open scoped KsIndex.KarcherData.ParameterAtlas
namespace KsIndex.KarcherData.DiskCompactification
variable {k m : ℕ} [h : Fact (2 ≤ k)] [NeZero m]

/-- Every point of the filled quotient has an open complex chart: the existing
EW quotient charts away from vertices, and the extended root charts at vertices. -/
theorem exists_surfaceChart (R : PaperHalfPeriodRealization k) (q : FilledChain k m) :
    ∃ e : OpenPartialHomeomorph (FilledChain k m) ℂ, q ∈ e.source := by
  classical
  by_cases hq : q ∈ regularSet
  · let p := (periodQuotientHomeomorph R).symm ⟨q, hq⟩
    let f := fun x => (periodQuotientHomeomorph (m := m) R x).val
    have hf : IsOpenEmbedding f :=
      regularSet_isOpen.isOpenEmbedding_subtypeVal.comp (periodQuotientHomeomorph R).isOpenEmbedding
    have : Nonempty (HeightLift.PeriodQuotient
        (extendedEWMap h.out (reflectionBasepoint k) R.C) m) := ⟨p⟩
    let e := hf.toOpenPartialHomeomorph f
    have he : f p = q := congrArg Subtype.val ((periodQuotientHomeomorph R).apply_symm_apply ⟨q,hq⟩)
    refine ⟨e.symm.trans (HeightLift.periodChart R.hC m p), ?_⟩
    change q ∈ e.target ∧ e.symm q ∈ (HeightLift.periodChart R.hC m p).source
    constructor
    · change q ∈ (hf.toOpenPartialHomeomorph f).target
      rw [Topology.IsOpenEmbedding.toOpenPartialHomeomorph_target]
      exact ⟨p,he⟩
    · rw [← he]
      change (hf.toOpenPartialHomeomorph f).symm (f p) ∈ _
      rw [hf.toOpenPartialHomeomorph_left_inv]
      exact HeightLift.periodChart_mem R.hC m p
  · have hp : (coordinate q).val ∈ Surface.punctures k := by
      simpa only [regularSet, Set.mem_ofPred_eq, not_not] using hq
    have he : q = vertex (coordinate q).val hp :=
      (coordinate_eq_vertex_iff _ hp q).mp rfl
    refine ⟨filledVertexChart R hp, ?_⟩
    exact (congrArg (fun x => x ∈ (filledVertexChart R hp).source) he).mpr
      (vertex_mem_filledVertexChart R hp)

/-- A chosen chart from the explicit regular and filled-end chart families. -/
def compactSurfaceChart (R : PaperHalfPeriodRealization k) (q : FilledChain k m) :
    OpenPartialHomeomorph (FilledChain k m) ℂ :=
  (exists_surfaceChart R q).choose

/-- The compact Hausdorff filling is locally a complex plane. No smoothness,
orientation or genus is asserted by this topological atlas. -/
@[instance_reducible]
def compactSurfaceChartedSpace (R : PaperHalfPeriodRealization k) :
    ChartedSpace ℂ (FilledChain k m) where
  atlas := Set.range (compactSurfaceChart R)
  chartAt := compactSurfaceChart R
  mem_chart_source q := (exists_surfaceChart R q).choose_spec
  chart_mem_atlas q := ⟨q,rfl⟩

/-- Compactness and the complex atlas give second countability. -/
instance : SecondCountableTopology (FilledChain k m) := by
  let R := Classical.choice (exists_paperHalfPeriodRealization (k := k))
  let := compactSurfaceChartedSpace (m := m) R
  exact ChartedSpace.secondCountable_of_sigmaCompact ℂ (FilledChain k m)

end KsIndex.KarcherData.DiskCompactification
