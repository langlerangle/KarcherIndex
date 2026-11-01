module

public import KsIndexLean.KarcherDiskEncoding

@[expose] public section


/-! Compact cores obtained by removing uniform neighborhoods of the ends. -/
noncomputable section
open Set Topology
namespace KsIndex.KarcherData
variable {k m : ℕ} [h : Fact (2 ≤ k)] [NeZero m]

def diskCore (k : ℕ) (ε : ℝ) : Set (PuncturedClosedDisk k) :=
  {w | ∀ p ∈ Surface.punctures k, ε ≤ ‖w.val.val - p‖}

lemma diskCore_isClosed (ε : ℝ) : IsClosed (diskCore k ε) := by
  have hV : IsEmbedding (fun w : PuncturedClosedDisk k => w.val.val) :=
    IsEmbedding.subtypeVal.comp IsEmbedding.subtypeVal
  have hc := hV.continuous
  simp only [diskCore, Set.ofPred_forall]
  apply isClosed_iInter
  intro p
  apply isClosed_iInter
  intro hp
  exact isClosed_le continuous_const
    ((hc.sub continuous_const).norm)

lemma diskCore_isCompact {ε : ℝ} (hε : 0 < ε) : IsCompact (diskCore k ε) := by
  let V : PuncturedClosedDisk k → ℂ := fun w => w.val.val
  have hV : IsEmbedding V := IsEmbedding.subtypeVal.comp IsEmbedding.subtypeVal
  apply hV.isCompact_iff.mpr
  have he : V '' diskCore k ε = Metric.closedBall (0 : ℂ) 1 ∩
      {w | ∀ p ∈ Surface.punctures k, ε ≤ ‖w - p‖} := by
    ext w
    constructor
    · rintro ⟨v, hv, rfl⟩
      exact ⟨by simpa only [Metric.mem_closedBall, dist_zero_right] using v.property, hv⟩
    · rintro ⟨hw, hp⟩
      have hn : w ∉ Surface.punctures k := by
        intro hwp
        have hx := hp w hwp
        simp only [sub_self, norm_zero] at hx
        linarith
      exact ⟨⟨⟨w, hn⟩, by simpa only [Metric.mem_closedBall, dist_zero_right] using hw⟩, hp, rfl⟩
  rw [he]
  apply (isCompact_closedBall (0 : ℂ) 1).inter_right
  simp only [diskCore, Set.ofPred_forall]
  apply isClosed_iInter
  intro p
  apply isClosed_iInter
  intro hp
  exact isClosed_le continuous_const ((continuous_id.sub continuous_const).norm)

namespace PaperHalfPeriodRealization

def periodCore (R : PaperHalfPeriodRealization k) (m : ℕ) [NeZero m] (ε : ℝ) :
    Set (HeightLift.PeriodQuotient (extendedEWMap h.out (reflectionBasepoint k) R.C) m) :=
  (fun p : ZMod (2 * m) × PuncturedClosedDisk k => R.orderedDiskPoint p.1 p.2) ''
    (Set.univ ×ˢ diskCore k ε)

lemma orderedDiskPoint_mem_periodCore_iff (R : PaperHalfPeriodRealization k)
    (ε : ℝ) (n : ZMod (2 * m)) (w : PuncturedClosedDisk k) :
    R.orderedDiskPoint n w ∈ R.periodCore m ε ↔ w ∈ diskCore k ε := by
  constructor
  · rintro ⟨⟨o,v⟩, hv, he⟩
    have hw := ((R.orderedDiskPoint_eq_iff_gluing (o,v) (n,w)).mp he).1
    change v = w at hw
    rw [← hw]
    exact hv.2
  · intro hw
    exact ⟨(n,w), ⟨Set.mem_univ _, hw⟩, rfl⟩

lemma periodCore_isClosed (R : PaperHalfPeriodRealization k) (ε : ℝ) :
    IsClosed (R.periodCore m ε) := by
  apply (isQuotientMap_iff_isClosed.mp R.orderedDiskMap_isQuotientMap).2 _ |>.mpr
  have he : (fun p : ZMod (2 * m) × PuncturedClosedDisk k => R.orderedDiskPoint p.1 p.2) ⁻¹'
      R.periodCore m ε = Set.univ ×ˢ diskCore k ε := by
    ext p
    simp only [Set.mem_preimage, orderedDiskPoint_mem_periodCore_iff,
      Set.mem_prod, Set.mem_univ, true_and]
  rw [he]
  exact isClosed_univ.prod (diskCore_isClosed ε)

lemma periodCore_isCompact (R : PaperHalfPeriodRealization k) {ε : ℝ} (hε : 0 < ε) :
    IsCompact (R.periodCore m ε) :=
  (isCompact_univ.prod (diskCore_isCompact hε)).image R.continuous_orderedDiskMap

lemma hasCompactSupport_descend_of_suppAwayP (R : PaperHalfPeriodRealization k)
    (u : ZMod (2 * m) → ℂ → ℂ) (hs : Surface.SeamVal k u)
    (hu : Surface.SuppAwayP k m u) :
    HasCompactSupport (R.diskFunctionDescend (restrictSeamFamily u hs)) := by
  obtain ⟨ε, hε, hu⟩ := hu
  apply HasCompactSupport.intro' (R.periodCore_isCompact (m := m) hε)
    (R.periodCore_isClosed ε)
  intro q hq
  obtain ⟨⟨n,w⟩, rfl⟩ := R.orderedDiskPoint_surjective q
  rw [R.orderedDiskPoint_mem_periodCore_iff] at hq
  change ¬ ∀ p ∈ Surface.punctures k, ε ≤ ‖w.val.val - p‖ at hq
  push Not at hq
  rw [diskFunctionDescend_apply]
  exact hu n w.val.val hq

end PaperHalfPeriodRealization
end KsIndex.KarcherData
