module

public import KsIndexLean.KarcherCompactSphereMap
public import KsIndexLean.KarcherCompactCellOrientation

@[expose] public section


/-! Forgetting the period label gives a map from the compact surface to the two-sphere. -/
noncomputable section
open Set Topology
namespace KsIndex.KarcherData.DiskCompactification
open PaperHalfPeriodRealization
variable {k m : ℕ} [h : Fact (2 ≤ k)] [NeZero m]

/-- Retain the parity of a face label and its disk coordinate. -/
def collapsePeriodCopies (p : Copies m) : Copies 1 := (Surface.parity m p.1, p.2)

omit [NeZero m] in
lemma collapsePeriodCopies_respects {p q : Copies m} (hpq : filledRel (k := k) p q) :
    filledRel (k := k) (collapsePeriodCopies p) (collapsePeriodCopies q) := by
  apply (filledRel_one_period _ _).mpr
  rcases hpq with ⟨hz, hp | hi | hn | hn⟩
  · exact ⟨hz, Or.inr (puncture_norm h.out hp)⟩
  · exact ⟨hz, Or.inl (congrArg (Surface.parity m) hi)⟩
  · exact ⟨hz, Or.inr hn.2.1⟩
  · exact ⟨hz, Or.inr hn.2.1⟩

omit [NeZero m] in
lemma continuous_collapsePeriodCopies : Continuous (collapsePeriodCopies (m := m)) := by
  exact ((continuous_of_discreteTopology : Continuous (Surface.parity m)).comp
    continuous_fst).prodMk continuous_snd

lemma collapsePeriodCopies_surjective : Function.Surjective (collapsePeriodCopies (m := m)) := by
  rintro ⟨i,z⟩
  have hi : i = 0 ∨ i = 1 := by
    fin_cases i <;> first | exact Or.inl rfl | exact Or.inr rfl
  rcases hi with rfl | rfl
  · refine ⟨(evenCopyIndex 0,z), ?_⟩
    exact Prod.ext (parity_evenCopyIndex 0) rfl
  · refine ⟨(oddCopyIndex 0,z), ?_⟩
    exact Prod.ext (parity_oddCopyIndex 0) rfl

/-- The continuous quotient map forgetting full periods. -/
def compactPeriodProjection : FilledChain k m → FilledChain k 1 :=
  Quotient.map collapsePeriodCopies (fun _ _ hpq => collapsePeriodCopies_respects hpq)

lemma continuous_compactPeriodProjection :
    Continuous (compactPeriodProjection (k := k) (m := m)) := by
  apply isQuotientMap_quotient_mk'.continuous_iff.mpr
  exact continuous_quotient_mk'.comp continuous_collapsePeriodCopies

lemma compactPeriodProjection_surjective :
    Function.Surjective (compactPeriodProjection (k := k) (m := m)) := by
  intro q
  induction q using Quotient.inductionOn with | h p =>
    obtain ⟨v, hv⟩ := collapsePeriodCopies_surjective (m := m) p
    exact ⟨Quotient.mk _ v, congrArg (Quotient.mk _) hv⟩

/-- The projection to the sphere obtained from the one-period compactification. -/
def compactSphereProjection :
    FilledChain k m → Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 :=
  onePeriodSphereMap ∘ compactPeriodProjection

lemma continuous_compactSphereProjection : Continuous (compactSphereProjection (k := k) (m := m)) :=
  continuous_onePeriodSphereMap.comp continuous_compactPeriodProjection

lemma compactSphereProjection_surjective :
    Function.Surjective (compactSphereProjection (k := k) (m := m)) :=
  onePeriodSphereMap_bijective.2.comp compactPeriodProjection_surjective

lemma compactPeriodProjection_coordinate (q : FilledChain k m) :
    coordinate (compactPeriodProjection q) = coordinate q := by
  induction q using Quotient.inductionOn with | h p => rfl

lemma compactPeriodProjection_vertex (w : ℂ) (hw : w ∈ Surface.punctures k) :
    compactPeriodProjection (m := m) (vertex w hw) = vertex w hw := by
  apply (coordinate_eq_vertex_iff w hw _).mp
  rw [compactPeriodProjection_coordinate]
  exact (coordinate_eq_vertex_iff w hw _).mpr rfl

/-- Every filled end point has exactly one preimage under period projection. -/
lemma compactPeriodProjection_eq_vertex_iff (q : FilledChain k m)
    (w : ℂ) (hw : w ∈ Surface.punctures k) :
    compactPeriodProjection q = vertex w hw ↔ q = vertex w hw := by
  rw [← coordinate_eq_vertex_iff w hw _, ← coordinate_eq_vertex_iff w hw _,
    compactPeriodProjection_coordinate]

lemma compactPeriodProjection_isQuotientMap :
    IsQuotientMap (compactPeriodProjection (k := k) (m := m)) :=
  continuous_compactPeriodProjection.isClosedMap.isQuotientMap
    continuous_compactPeriodProjection compactPeriodProjection_surjective

lemma compactPeriodProjection_face (i : ZMod (2 * m)) (z : ClosedDisk) :
    compactPeriodProjection (k := k) (faceMap i z) = faceMap (Surface.parity m i) z := rfl

/-- Away from the equator, fibers are exactly the face labels of a fixed parity. -/
lemma compactPeriodProjection_interior_fiber (j : ZMod (2 * 1)) (z : ClosedDisk)
    (hz : ‖z.val‖ < 1) (q : FilledChain k m) :
    compactPeriodProjection q = faceMap j z ↔
      ∃ i : ZMod (2 * m), Surface.parity m i = j ∧ q = faceMap i z := by
  induction q using Quotient.inductionOn with | h p =>
    rcases p with ⟨i,v⟩
    constructor
    · intro he
      have hh := (faceMap_eq_of_interior (k := k) hz).mp he.symm
      exact ⟨i, hh.1.symm, congrArg (faceMap i) hh.2.symm⟩
    · rintro ⟨a, ha, he⟩
      rw [he, compactPeriodProjection_face, ha]

/-- The upper-hemisphere fiber is enumerated without repetitions by full-period labels. -/
lemma compactPeriodProjection_upper_fiber (z : ClosedDisk) (hz : ‖z.val‖ < 1)
    (q : FilledChain k m) :
    compactPeriodProjection q = faceMap 0 z ↔
      ∃ j : ZMod m, q = faceMap (evenCopyIndex j) z := by
  rw [compactPeriodProjection_interior_fiber 0 z hz]
  constructor
  · rintro ⟨i,hi,hq⟩
    obtain ⟨j,rfl | rfl⟩ := copyIndex_cases i
    · exact ⟨j,hq⟩
    · rw [parity_oddCopyIndex] at hi
      exact (one_ne_zero hi).elim
  · rintro ⟨j,rfl⟩
    exact ⟨evenCopyIndex j, parity_evenCopyIndex j, rfl⟩

lemma compactPeriodProjection_lower_fiber (z : ClosedDisk) (hz : ‖z.val‖ < 1)
    (q : FilledChain k m) :
    compactPeriodProjection q = faceMap 1 z ↔
      ∃ j : ZMod m, q = faceMap (oddCopyIndex j) z := by
  rw [compactPeriodProjection_interior_fiber 1 z hz]
  constructor
  · rintro ⟨i,hi,hq⟩
    obtain ⟨j,rfl | rfl⟩ := copyIndex_cases i
    · rw [parity_evenCopyIndex] at hi
      exact (zero_ne_one hi).elim
    · exact ⟨j,hq⟩
  · rintro ⟨j,rfl⟩
    exact ⟨oddCopyIndex j, parity_oddCopyIndex j, rfl⟩

/-- Full-period labels identify the fiber over an upper-hemisphere point. -/
def upperPeriodFiberEquiv (z : ClosedDisk) (hz : ‖z.val‖ < 1) :
    ZMod m ≃ {q : FilledChain k m // compactPeriodProjection q = faceMap 0 z} :=
  Equiv.ofBijective (fun j => ⟨faceMap (evenCopyIndex j) z, by
    rw [compactPeriodProjection_face, parity_evenCopyIndex]⟩) (by
    constructor
    · intro a b he
      apply evenCopyIndex_injective
      exact ((faceMap_eq_of_interior hz).mp (congrArg Subtype.val he)).1
    · rintro ⟨q,hq⟩
      obtain ⟨j,hj⟩ := (compactPeriodProjection_upper_fiber z hz q).mp hq
      exact ⟨j, Subtype.ext hj.symm⟩)

/-- Full-period labels identify the fiber over a lower-hemisphere point. -/
def lowerPeriodFiberEquiv (z : ClosedDisk) (hz : ‖z.val‖ < 1) :
    ZMod m ≃ {q : FilledChain k m // compactPeriodProjection q = faceMap 1 z} :=
  Equiv.ofBijective (fun j => ⟨faceMap (oddCopyIndex j) z, by
    rw [compactPeriodProjection_face, parity_oddCopyIndex]⟩) (by
    constructor
    · intro a b he
      have hi := ((faceMap_eq_of_interior hz).mp (congrArg Subtype.val he)).1
      rw [← evenCopyIndex_succ, ← evenCopyIndex_succ] at hi
      exact evenCopyIndex_injective (add_right_cancel hi)
    · rintro ⟨q,hq⟩
      obtain ⟨j,hj⟩ := (compactPeriodProjection_lower_fiber z hz q).mp hq
      exact ⟨j, Subtype.ext hj.symm⟩)

lemma upperPeriodFiber_card (z : ClosedDisk) (hz : ‖z.val‖ < 1) :
    Nat.card {q : FilledChain k m // compactPeriodProjection q = faceMap 0 z} = m := by
  rw [← Nat.card_congr (upperPeriodFiberEquiv (k := k) (m := m) z hz)]
  simpa only [Nat.card_eq_fintype_card] using ZMod.card m

lemma lowerPeriodFiber_card (z : ClosedDisk) (hz : ‖z.val‖ < 1) :
    Nat.card {q : FilledChain k m // compactPeriodProjection q = faceMap 1 z} = m := by
  rw [← Nat.card_congr (lowerPeriodFiberEquiv (k := k) (m := m) z hz)]
  simpa only [Nat.card_eq_fintype_card] using ZMod.card m

end KsIndex.KarcherData.DiskCompactification
