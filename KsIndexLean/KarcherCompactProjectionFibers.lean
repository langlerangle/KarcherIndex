module

public import KsIndexLean.KarcherCompactSphereProjection

@[expose] public section


/-! Exact fiber counts for the projection of the compactified surface to one period. -/
noncomputable section
open Set Topology
namespace KsIndex.KarcherData.DiskCompactification
open PaperHalfPeriodRealization
variable {k m : ℕ} [h : Fact (2 ≤ k)] [NeZero m]

lemma compactPeriodProjection_equator_fiber (z : ClosedDisk) (hz : ‖z.val‖ = 1)
    (hp : z.val ∉ Surface.punctures k) (q : FilledChain k m) :
    compactPeriodProjection q = faceMap 0 z ↔
      ∃ j : ZMod m, q = faceMap (evenCopyIndex j) z := by
  constructor
  · intro he
    have hc : coordinate q = z := by
      have hh := congrArg coordinate he
      rw [compactPeriodProjection_coordinate] at hh
      exact hh
    have hq : q ∈ ⋃ p : ZMod m × Fin (2 * k), openEdge p := by
      rw [openEdges_cover]
      exact ⟨hc ▸ hz, hc ▸ hp⟩
    obtain ⟨p,s,hs⟩ := Set.mem_iUnion.mp hq
    have hcoord := congrArg coordinate hs
    change edgeParameter (p.2.val : ℤ) s.val = coordinate q at hcoord
    refine ⟨p.1, ?_⟩
    rw [← hs]
    change faceMap (evenCopyIndex p.1) (edgeParameter (p.2.val : ℤ) s.val) = _
    rw [hcoord, hc]
  · rintro ⟨j,rfl⟩
    rw [compactPeriodProjection_face, parity_evenCopyIndex]

/-- The nonvertex equatorial fiber has one point per full-period label. -/
def equatorPeriodFiberEquiv (z : ClosedDisk) (hz : ‖z.val‖ = 1)
    (hp : z.val ∉ Surface.punctures k) :
    ZMod m ≃ {q : FilledChain k m // compactPeriodProjection q = faceMap 0 z} :=
  Equiv.ofBijective (fun j => ⟨faceMap (evenCopyIndex j) z, by
    rw [compactPeriodProjection_face, parity_evenCopyIndex]⟩) (by
    constructor
    · intro a b he
      exact evenFace_eq_index hp (congrArg Subtype.val he)
    · rintro ⟨q,hq⟩
      obtain ⟨j,hj⟩ := (compactPeriodProjection_equator_fiber z hz hp q).mp hq
      exact ⟨j, Subtype.ext hj.symm⟩)

lemma equatorPeriodFiber_card (z : ClosedDisk) (hz : ‖z.val‖ = 1)
    (hp : z.val ∉ Surface.punctures k) :
    Nat.card {q : FilledChain k m // compactPeriodProjection q = faceMap 0 z} = m := by
  rw [← Nat.card_congr (equatorPeriodFiberEquiv (k := k) (m := m) z hz hp)]
  simpa only [Nat.card_eq_fintype_card] using ZMod.card m

/-- Every fiber outside the filled end points has exactly `m` points. -/
theorem compactPeriodProjection_fiber_card (q : FilledChain k 1)
    (hp : (coordinate q).val ∉ Surface.punctures k) :
    Nat.card {v : FilledChain k m // compactPeriodProjection v = q} = m := by
  induction q using Quotient.inductionOn with | h p =>
    rcases p with ⟨i,z⟩
    change z.val ∉ Surface.punctures k at hp
    change Nat.card {v : FilledChain k m // compactPeriodProjection v = faceMap i z} = m
    by_cases hz : ‖z.val‖ < 1
    · have hi : i = 0 ∨ i = 1 := by
        fin_cases i <;> first | exact Or.inl rfl | exact Or.inr rfl
      rcases hi with rfl | rfl
      · exact upperPeriodFiber_card z hz
      · exact lowerPeriodFiber_card z hz
    · have hn : ‖z.val‖ = 1 := le_antisymm z.property (le_of_not_gt hz)
      have he : faceMap (k := k) i z = faceMap 0 z := by
        apply Quotient.sound
        exact (filledRel_one_period _ _).mpr ⟨rfl, Or.inr hn⟩
      rw [he]
      exact equatorPeriodFiber_card z hn hp

/-- The fiber over every filled end point has cardinality one. -/
theorem compactPeriodProjection_vertex_fiber_card (w : ℂ) (hw : w ∈ Surface.punctures k) :
    Nat.card {q : FilledChain k m // compactPeriodProjection q = vertex w hw} = 1 := by
  apply Nat.card_eq_one_iff_exists.mpr
  refine ⟨⟨vertex w hw, compactPeriodProjection_vertex w hw⟩, ?_⟩
  intro q
  exact Subtype.ext ((compactPeriodProjection_eq_vertex_iff q.val w hw).mp q.property)

end KsIndex.KarcherData.DiskCompactification
