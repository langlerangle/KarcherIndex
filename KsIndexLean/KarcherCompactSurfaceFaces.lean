module

public import KsIndexLean.KarcherCompactSurfaceConnected

@[expose] public section


/-! The actual closed disk faces and their disjoint open interiors. -/
noncomputable section
open Set Topology
namespace KsIndex.KarcherData.DiskCompactification
variable {k m : ℕ} [h : Fact (2 ≤ k)] [NeZero m]

/-- The characteristic map of a disk copy in the filled quotient. -/
def faceMap (i : ZMod (2 * m)) (z : ClosedDisk) : FilledChain k m :=
  Quotient.mk (filledSetoid k m) (i,z)

lemma continuous_faceMap (i : ZMod (2 * m)) : Continuous (faceMap (k := k) i) :=
  continuous_quotient_mk'.comp (continuous_const.prodMk continuous_id)

lemma faceMap_injective (i : ZMod (2 * m)) : Function.Injective (faceMap (k := k) i) := by
  intro z v he
  exact (Quotient.exact he).1

lemma faceMap_isClosedEmbedding (i : ZMod (2 * m)) :
    IsClosedEmbedding (faceMap (k := k) i) :=
  (continuous_faceMap i).isClosedEmbedding (faceMap_injective i)

/-- Each entire closed face is a genuine embedded closed disk. -/
def faceHomeomorph (i : ZMod (2 * m)) : ClosedDisk ≃ₜ Set.range (faceMap (k := k) i) :=
  (faceMap_isClosedEmbedding i).isEmbedding.toHomeomorph

def openFace (i : ZMod (2 * m)) : Set (FilledChain k m) :=
  faceMap i '' {z : ClosedDisk | ‖z.val‖ < 1}

/-- Interior points have no identifications with any other disk copy. -/
lemma faceMap_eq_of_interior {i j : ZMod (2 * m)} {z v : ClosedDisk}
    (hz : ‖z.val‖ < 1) : faceMap (k := k) i z = faceMap j v ↔ i = j ∧ z = v := by
  constructor
  · intro he
    have hh := Quotient.exact he
    have hp : z.val ∉ Surface.punctures k := by
      intro hp
      exact (ne_of_lt hz) (puncture_norm h.out hp)
    have ha (n : ZMod (2 * m)) : z.val ∉ Surface.seamArc k m n := by
      intro ha
      exact (ne_of_lt hz) ha.1
    have hi : i = j := by
      simpa only [filledSetoid, filledRel, hp, ha, false_or, and_false, or_false] using hh.2
    exact ⟨hi, hh.1⟩
  · rintro ⟨rfl,rfl⟩
    rfl

lemma openFace_preimage (i : ZMod (2 * m)) :
    Quotient.mk (filledSetoid k m) ⁻¹' openFace i =
      {p : Copies m | p.1 = i ∧ ‖p.2.val‖ < 1} := by
  ext p
  constructor
  · rintro ⟨z,hz,he⟩
    have hh := (faceMap_eq_of_interior hz).mp he
    exact ⟨hh.1.symm, hh.2 ▸ hz⟩
  · rintro ⟨hi,hz⟩
    refine ⟨p.2,hz,?_⟩
    change Quotient.mk (filledSetoid k m) (i,p.2) = Quotient.mk _ p
    exact congrArg (Quotient.mk (filledSetoid k m)) (Prod.ext hi.symm rfl)

lemma isOpen_openFace (i : ZMod (2 * m)) : IsOpen (openFace (k := k) i) := by
  apply isQuotientMap_quotient_mk'.isOpen_preimage.mp
  change IsOpen (Quotient.mk (filledSetoid k m) ⁻¹' openFace i)
  rw [openFace_preimage]
  have hi : IsOpen {p : Copies m | p.1 = i} :=
    (isOpen_discrete ({i} : Set (ZMod (2 * m)))).preimage continuous_fst
  exact hi.inter (isOpen_lt (continuous_subtype_val.comp continuous_snd).norm continuous_const)

lemma openFaces_pairwiseDisjoint :
    Pairwise (fun i j => Disjoint (openFace (k := k) (m := m) i) (openFace j)) := by
  intro i j hij
  apply Set.disjoint_left.mpr
  rintro q ⟨z,hz,hzq⟩ ⟨v,hv,hvq⟩
  exact hij ((faceMap_eq_of_interior hz).mp (hzq.trans hvq.symm)).1

/-- The finitely many closed faces cover the actual compact surface. -/
theorem closedFaces_cover : ⋃ i : ZMod (2 * m), Set.range (faceMap (k := k) i) = Set.univ := by
  apply Set.eq_univ_of_forall
  intro q
  obtain ⟨p,rfl⟩ := Quotient.mk_surjective q
  exact Set.mem_iUnion.mpr ⟨p.1, p.2, rfl⟩

lemma openFace_nonempty (i : ZMod (2 * m)) : (openFace (k := k) i).Nonempty :=
  ⟨faceMap i ⟨0, by simp⟩, ⟨⟨0,by simp⟩,by simp,rfl⟩⟩

lemma openFace_injective : Function.Injective (openFace (k := k) (m := m)) := by
  intro i j he
  have hm : faceMap (k := k) i ⟨0,by simp⟩ ∈ openFace i :=
    ⟨⟨0,by simp⟩,by simp,rfl⟩
  rw [he] at hm
  obtain ⟨v,hv,heq⟩ := hm
  exact ((faceMap_eq_of_interior (by simp : ‖(0 : ℂ)‖ < 1)).mp heq.symm).1

/-- The actual collection of distinct open faces has cardinality `2m`. -/
theorem openFace_card : Nat.card (Set.range (openFace (k := k) (m := m))) = 2 * m := by
  have : NeZero (2 * m) := ⟨Nat.mul_ne_zero (by decide) (NeZero.ne m)⟩
  rw [← Nat.card_congr (Equiv.ofInjective _ (openFace_injective (k := k) (m := m)))]
  simpa only [Nat.card_eq_fintype_card] using ZMod.card (2 * m)

/-- The part remaining after removal of the face interiors is precisely the
image of the unit-circle boundaries. -/
theorem not_mem_openFaces_iff (q : FilledChain k m) :
    q ∉ ⋃ i : ZMod (2 * m), openFace i ↔ ‖(coordinate q).val‖ = 1 := by
  induction q using Quotient.inductionOn with
  | h p =>
    change Quotient.mk (filledSetoid k m) p ∉ ⋃ i, openFace i ↔ ‖p.2.val‖ = 1
    constructor
    · intro hn
      apply le_antisymm p.2.property
      by_contra hlt
      have hz : ‖p.2.val‖ < 1 := lt_of_not_ge hlt
      exact hn (Set.mem_iUnion.mpr ⟨p.1, p.2, hz, rfl⟩)
    · intro he hm
      obtain ⟨i,z,hz,hq⟩ := Set.mem_iUnion.mp hm
      have hh := (Quotient.exact hq).1
      have hez : ‖z.val‖ = 1 :=
        (congrArg (fun v : ClosedDisk => ‖v.val‖) hh).trans he
      exact (ne_of_lt hz) hez

/-- Each open face has the topology of the open disk, inherited from its
embedded closed disk. -/
def openFaceHomeomorph (i : ZMod (2 * m)) :
    {z : ClosedDisk // ‖z.val‖ < 1} ≃ₜ openFace (k := k) i :=
  ((faceMap_isClosedEmbedding (k := k) i).isEmbedding.comp
    IsEmbedding.subtypeVal).toHomeomorph.trans
      (Homeomorph.setCongr (by
        ext q
        constructor
        · rintro ⟨z,rfl⟩
          exact ⟨z.val,z.property,rfl⟩
        · rintro ⟨z,hz,rfl⟩
          exact ⟨⟨z,hz⟩,rfl⟩))

/-- Distinct faces meet only at filled vertices or at the prescribed seams.
Both seam alternatives remain present when the period has just two faces. -/
theorem faceMap_eq_iff_boundary {i j : ZMod (2 * m)} (hij : i ≠ j)
    (z v : ClosedDisk) : faceMap (k := k) i z = faceMap j v ↔
      z = v ∧ (z.val ∈ Surface.punctures k ∨
        (j = i + 1 ∧ z.val ∈ Surface.seamArc k m i) ∨
        (i = j + 1 ∧ z.val ∈ Surface.seamArc k m j)) := by
  change Quotient.mk (filledSetoid k m) (i,z) = Quotient.mk _ (j,v) ↔ _
  rw [Quotient.eq]
  change filledRel (k := k) (i,z) (j,v) ↔ _
  simp only [filledRel, hij, false_or]

/-- The one-dimensional boundary set is covered by the actual face circles. -/
theorem faceCircles_cover_boundary :
    (⋃ i : ZMod (2 * m), faceMap (k := k) i '' {z : ClosedDisk | ‖z.val‖ = 1}) =
      {q : FilledChain k m | ‖(coordinate q).val‖ = 1} := by
  ext q
  constructor
  · intro hm
    obtain ⟨i,z,hz,rfl⟩ := Set.mem_iUnion.mp hm
    exact hz
  · intro hq
    obtain ⟨p,rfl⟩ := Quotient.mk_surjective q
    exact Set.mem_iUnion.mpr ⟨p.1,p.2,hq,rfl⟩

end KsIndex.KarcherData.DiskCompactification
