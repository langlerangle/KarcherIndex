module

public import KsIndexLean.KarcherDiskGluingTopology
public import KsIndexLean.CompactClosedQuotient
public import KsIndexLean.EnergySmoothBound

@[expose] public section


/-! Filling the deleted vertices in the cyclic EW disk gluing. -/
noncomputable section
namespace KsIndex.KarcherData.DiskCompactification
open Set
variable {k m : ℕ} [h : Fact (2 ≤ k)] [NeZero m]
abbrev ClosedDisk := {w : ℂ // ‖w‖ ≤ 1}
abbrev Copies (m : ℕ) := ZMod (2 * m) × ClosedDisk

def filledRel (p q : Copies m) : Prop :=
  p.2 = q.2 ∧ (p.2.val ∈ Surface.punctures k ∨ p.1 = q.1 ∨
    (q.1 = p.1 + 1 ∧ p.2.val ∈ Surface.seamArc k m p.1) ∨
    (p.1 = q.1 + 1 ∧ p.2.val ∈ Surface.seamArc k m q.1))

omit h [NeZero m] in
lemma filledRel_same {i j : ZMod (2 * m)} (w : ClosedDisk)
    (hw : w.val ∉ Surface.punctures k) :
    filledRel (k := k) (i,w) (j,w) ↔
      diskGluingRel (i,(⟨⟨w.val,hw⟩,w.property⟩ : PuncturedClosedDisk k))
        (j,(⟨⟨w.val,hw⟩,w.property⟩ : PuncturedClosedDisk k)) := by
  simp only [filledRel, diskGluingRel, hw, false_or, true_and]
  exact ⟨fun hh => ⟨rfl, hh⟩, fun hh => hh.2⟩

lemma filledRel_equivalence : Equivalence (filledRel (k := k) (m := m)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro p
    exact ⟨rfl, Or.inr (Or.inl rfl)⟩
  · rintro ⟨i,w⟩ ⟨j,v⟩ ⟨hw, hp⟩
    dsimp only at hw
    subst v
    by_cases he : w.val ∈ Surface.punctures k
    · exact ⟨rfl, Or.inl he⟩
    · exact (filledRel_same w he).mpr (diskGluingRel_symm ((filledRel_same w he).mp ⟨rfl,hp⟩))
  · rintro ⟨i,w⟩ ⟨j,v⟩ ⟨l,u⟩ ⟨hw,hp⟩ ⟨hv,hq⟩
    dsimp only at hw hv
    subst v
    subst u
    by_cases he : w.val ∈ Surface.punctures k
    · exact ⟨rfl, Or.inl he⟩
    · apply (filledRel_same w he).mpr
      exact (diskGluingSetoid k m).trans
        ((filledRel_same (i := i) (j := j) w he).mp ⟨rfl,hp⟩)
        ((filledRel_same (i := j) (j := l) w he).mp ⟨rfl,hq⟩)

def filledSetoid (k m : ℕ) [Fact (2 ≤ k)] [NeZero m] : Setoid (Copies m) :=
  ⟨filledRel (k := k), filledRel_equivalence (k := k)⟩

abbrev FilledChain (k m : ℕ) [Fact (2 ≤ k)] [NeZero m] := Quotient (filledSetoid k m)

instance : CompactSpace ClosedDisk := by
  have he : {w : ℂ | ‖w‖ ≤ 1} = Metric.closedBall 0 1 := by ext w; simp
  apply isCompact_iff_compactSpace.mp
  change IsCompact {w : ℂ | ‖w‖ ≤ 1}
  rw [he]
  exact isCompact_closedBall (0 : ℂ) 1

instance : CompactSpace (FilledChain k m) := by
  have : NeZero (2 * m) := ⟨Nat.mul_ne_zero (by decide) (NeZero.ne m)⟩
  infer_instance

/-- All disk copies of a given missing endpoint become one point; distinct
endpoint coordinates never become identified. -/
lemma filled_vertex_eq_iff (i j : ZMod (2 * m)) (w v : ClosedDisk)
    (hw : w.val ∈ Surface.punctures k) :
    (Quotient.mk (filledSetoid k m) (i,w) = Quotient.mk _ (j,v)) ↔ w = v := by
  constructor
  · intro he
    exact (Quotient.exact he).1
  · rintro rfl
    exact Quotient.sound ⟨rfl,Or.inl hw⟩

theorem filledChain_compact : IsCompact (Set.univ : Set (FilledChain k m)) :=
  isCompact_univ

omit h [NeZero m] in
/-- Closing a seam adds only punctures, which are already identified in every copy. -/
lemma filledRel_closed_formula (p q : Copies m) :
    filledRel (k := k) p q ↔
      p.2 = q.2 ∧ (p.2.val ∈ Surface.punctures k ∨ p.1 = q.1 ∨
        (q.1 = p.1 + 1 ∧ ‖p.2.val‖ = 1 ∧
          (-1 : ℝ) ^ (Surface.parity m (p.1 + 1)).val * (p.2.val ^ k).re ≤ 0) ∨
        (p.1 = q.1 + 1 ∧ ‖p.2.val‖ = 1 ∧
          (-1 : ℝ) ^ (Surface.parity m (q.1 + 1)).val * (p.2.val ^ k).re ≤ 0)) := by
  by_cases hp : p.2.val ∈ Surface.punctures k
  · simp [filledRel, hp]
  have hs (i : ZMod (2 * m)) :
      p.2.val ∈ Surface.seamArc k m i ↔
        ‖p.2.val‖ = 1 ∧
          (-1 : ℝ) ^ (Surface.parity m (i + 1)).val * (p.2.val ^ k).re ≤ 0 := by
    change (_ ∧ _ < 0) ↔ (_ ∧ _ ≤ 0)
    constructor
    · exact fun hh => ⟨hh.1, le_of_lt hh.2⟩
    · intro hh
      refine ⟨hh.1, lt_of_le_of_ne hh.2 ?_⟩
      exact mul_ne_zero (pow_ne_zero _ (by norm_num))
        (KsIndex.FaithfulInjection.circle_not_puncture_re_ne hh.1 hp)
  simp only [filledRel, hs]

omit h [NeZero m] in
/-- The equivalence relation remains closed when all copies of each deleted
endpoint are filled by a single vertex. -/
theorem filledRel_isClosed : IsClosed {p : Copies m × Copies m | filledRel (k := k) p.1 p.2} := by
  have hc (f : ZMod (2 * m) → ℝ) : Continuous f := continuous_of_discreteTopology
  have hadd : Continuous (fun i : ZMod (2 * m) => i + 1) := continuous_of_discreteTopology
  have hw : Continuous (fun p : Copies m × Copies m => p.1.2.val) := by fun_prop
  have hz := hw.pow k
  have hre := Complex.continuous_re.comp hz
  have hnorm := isClosed_eq hw.norm continuous_const (g := fun _ => (1 : ℝ))
  have hpunc : IsClosed {p : Copies m × Copies m | p.1.2.val ∈ Surface.punctures k} :=
    isClosed_eq (hw.pow (2 * k)) continuous_const
  have hleft := isClosed_le (g := fun _ => (0 : ℝ))
    (((hc (fun i => (-1 : ℝ) ^ (Surface.parity m (i + 1)).val)).comp
      (continuous_fst.comp continuous_fst)).mul hre) continuous_const
  have hright := isClosed_le (g := fun _ => (0 : ℝ))
    (((hc (fun i => (-1 : ℝ) ^ (Surface.parity m (i + 1)).val)).comp
      (continuous_fst.comp continuous_snd)).mul hre) continuous_const
  have hcoord : IsClosed {p : Copies m × Copies m | p.1.2 = p.2.2} :=
    isClosed_eq (continuous_snd.comp continuous_fst) (continuous_snd.comp continuous_snd)
  have heq : IsClosed {p : Copies m × Copies m | p.1.1 = p.2.1} :=
    isClosed_eq (continuous_fst.comp continuous_fst) (continuous_fst.comp continuous_snd)
  have hl : IsClosed {p : Copies m × Copies m | p.2.1 = p.1.1 + 1} :=
    isClosed_eq (continuous_fst.comp continuous_snd)
      (hadd.comp (continuous_fst.comp continuous_fst))
  have hr : IsClosed {p : Copies m × Copies m | p.1.1 = p.2.1 + 1} :=
    isClosed_eq (continuous_fst.comp continuous_fst)
      (hadd.comp (continuous_fst.comp continuous_snd))
  convert hcoord.inter (hpunc.union (heq.union
    ((hl.inter (hnorm.inter hleft)).union (hr.inter (hnorm.inter hright))))) using 1
  ext p
  exact filledRel_closed_formula p.1 p.2

instance : T2Space (FilledChain k m) := by
  have : NeZero (2 * m) := ⟨Nat.mul_ne_zero (by decide) (NeZero.ne m)⟩
  exact t2Space_quotient_of_closed_relation (filledSetoid k m) filledRel_isClosed

end KsIndex.KarcherData.DiskCompactification
