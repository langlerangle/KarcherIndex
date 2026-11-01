module

public import KsIndexLean.KarcherDiskCompactification
public import KsIndexLean.KarcherCompactSupportConverse

@[expose] public section


/-! Neighborhoods of the added vertices are detected by the folded planar coordinate. -/
noncomputable section
open Set Topology Filter
namespace KsIndex.KarcherData.DiskCompactification
variable {k m : ℕ} [h : Fact (2 ≤ k)] [NeZero m]

/-- The added point with a specified puncture coordinate. -/
def vertex (w : ℂ) (hw : w ∈ Surface.punctures k) : FilledChain k m :=
  Quotient.mk (filledSetoid k m) (0, ⟨w, le_of_eq (puncture_norm h.out hw)⟩)

@[simp] lemma coordinate_vertex (w : ℂ) (hw : w ∈ Surface.punctures k) :
    (coordinate (vertex (m := m) w hw)).val = w := rfl

/-- A puncture coordinate has a single fiber, even though ordinary coordinates
can have several sheets. -/
lemma coordinate_eq_vertex_iff (w : ℂ) (hw : w ∈ Surface.punctures k)
    (q : FilledChain k m) : (coordinate q).val = w ↔ q = vertex w hw := by
  constructor
  · induction q using Quotient.inductionOn with
    | h p =>
      intro he
      apply Quotient.sound
      refine ⟨Subtype.ext he, Or.inl ?_⟩
      change p.2.val = w at he
      exact he ▸ hw
  · rintro rfl
    rfl

/-- Every neighborhood of an added vertex contains a full coordinate
neighborhood, simultaneously in all of the incident disk copies. -/
theorem exists_coordinate_ball_subset (w : ℂ) (hw : w ∈ Surface.punctures k)
    {U : Set (FilledChain k m)} (hU : IsOpen U) (hv : vertex w hw ∈ U) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ q : FilledChain k m,
      dist (coordinate q).val w < ε → q ∈ U := by
  let f : FilledChain k m → ℂ := fun q => (coordinate q).val
  have hf : Continuous f := continuous_subtype_val.comp continuous_coordinate
  have hc : IsClosed (f '' Uᶜ) := (hU.isClosed_compl.isCompact.image hf).isClosed
  have hn : w ∈ (f '' Uᶜ)ᶜ := by
    rintro ⟨q, hq, he⟩
    have heq := (coordinate_eq_vertex_iff w hw q).mp he
    exact hq (heq.symm ▸ hv)
  obtain ⟨ε, hε, hsub⟩ := Metric.isOpen_iff.mp hc.isOpen_compl w hn
  refine ⟨ε, hε, ?_⟩
  intro q hq
  by_contra hnq
  exact hsub hq ⟨q, hnq, rfl⟩

/-- Convergence to an added vertex is equivalent to convergence of its planar
coordinate. This criterion applies to arbitrary filters, not only sequences. -/
theorem tendsto_vertex_iff {α : Type*} {l : Filter α} {f : α → FilledChain k m}
    (w : ℂ) (hw : w ∈ Surface.punctures k) :
    Tendsto f l (𝓝 (vertex w hw)) ↔
      Tendsto (fun a => (coordinate (f a)).val) l (𝓝 w) := by
  constructor
  · intro hf
    exact (continuous_subtype_val.comp continuous_coordinate).continuousAt.tendsto.comp hf
  · intro hf
    apply tendsto_nhds.mpr
    intro U hU hv
    obtain ⟨ε, hε, he⟩ := exists_coordinate_ball_subset w hw hU hv
    have hh := hf (Metric.ball_mem_nhds w hε)
    exact Filter.mem_of_superset hh (fun a ha => he (f a) ha)

/-- The compactification coordinate extends the existing folded coordinate on
 the actual EW quotient. -/
lemma coordinate_periodQuotientHomeomorph (R : PaperHalfPeriodRealization k)
    (q : HeightLift.PeriodQuotient (extendedEWMap h.out (reflectionBasepoint k) R.C) m) :
    (coordinate (periodQuotientHomeomorph R q).val).val = R.foldedDiskCoordinate q := by
  obtain ⟨p, rfl⟩ := R.orderedDiskPoint_surjective q
  rw [R.foldedDiskCoordinate_apply]
  have he : R.gluedDiskHomeomorph.symm (R.orderedDiskPoint p.1 p.2) =
      Quotient.mk (diskGluingSetoid k m) p :=
    R.gluedDiskHomeomorph.symm_apply_apply (Quotient.mk (diskGluingSetoid k m) p)
  change (coordinate (regularHomeomorph
    (R.gluedDiskHomeomorph.symm (R.orderedDiskPoint p.1 p.2))).val).val = p.2.val.val
  rw [he]
  rfl

/-- The vertex convergence criterion expressed directly on the EW quotient. -/
theorem tendsto_periodQuotient_vertex_iff (R : PaperHalfPeriodRealization k)
    {α : Type*} {l : Filter α}
    {f : α → HeightLift.PeriodQuotient (extendedEWMap h.out (reflectionBasepoint k) R.C) m}
    (w : ℂ) (hw : w ∈ Surface.punctures k) :
    Tendsto (fun a => (periodQuotientHomeomorph R (f a)).val) l (𝓝 (vertex w hw)) ↔
      Tendsto (fun a => R.foldedDiskCoordinate (f a)) l (𝓝 w) := by
  rw [tendsto_vertex_iff]
  simp only [coordinate_periodQuotientHomeomorph]

end KsIndex.KarcherData.DiskCompactification
