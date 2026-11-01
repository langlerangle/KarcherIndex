module

public import KsIndexLean.ChainPhaseExtraction
public import KsIndexLean.TwistedPair

@[expose] public section


open Set MeasureTheory
noncomputable section
namespace KsIndex.Trace
open KsIndex.WeakH1

/-- Upper/lower input pair; even copies carry lower, odd copies upper. -/
def weakPhaseCopies (m : ℕ) (c : ℂ) (p : ComplexH1 × ComplexH1)
    (n : ZMod (2 * m)) : ComplexH1 :=
  c ^ (n.val / 2) • if n.val % 2 = 0 then p.2 else p.1

lemma weakPhaseCopies_zero (m : ℕ) [NeZero m] (c : ℂ) (p : ComplexH1 × ComplexH1) :
    weakPhaseCopies m c p 0 = p.2 := by simp [weakPhaseCopies]

lemma weakPhaseCopies_one (m : ℕ) [NeZero m] (c : ℂ) (p : ComplexH1 × ComplexH1) :
    weakPhaseCopies m c p 1 = p.1 := by
  let : Fact (1 < 2 * m) := ⟨by have := NeZero.ne m; omega⟩
  simp [weakPhaseCopies, ZMod.val_one]

lemma weakPhaseCopies_shift (m : ℕ) [NeZero m] (c : ℂ) (hc : c ^ m = 1)
    (p : ComplexH1 × ComplexH1) (n : ZMod (2 * m)) :
    weakPhaseCopies m c p (n + 2) = c • weakPhaseCopies m c p n := by
  let : NeZero (2 * m) := ⟨by have := NeZero.ne m; omega⟩
  have hlt := ZMod.val_lt n
  have hval : (n + 2).val = (n.val + 2) % (2 * m) := by
    rw [ZMod.val_add, ZMod.val_two_eq_two_mod, Nat.add_mod_mod]
  unfold weakPhaseCopies
  by_cases hwrap : n.val + 2 < 2 * m
  · rw [hval, Nat.mod_eq_of_lt hwrap]
    have h1 : (n.val + 2) / 2 = n.val / 2 + 1 := by omega
    have h2 : (n.val + 2) % 2 = n.val % 2 := by omega
    rw [h1, h2, pow_succ', mul_smul]
  · have h0 : (n + 2).val = n.val + 2 - 2 * m := by
      rw [hval]
      have hh : n.val + 2 - 2 * m < 2 * m := by omega
      conv_lhs => rw [show n.val + 2 = (n.val + 2 - 2 * m) + 1 * (2 * m) by omega]
      rw [Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hh]
    have h1 : n.val / 2 + 1 = (n.val + 2 - 2 * m) / 2 + m := by omega
    have h2 : (n.val + 2 - 2 * m) % 2 = n.val % 2 := by omega
    rw [h0, h2, ← mul_smul, ← pow_succ', h1, pow_add, hc, mul_one]

set_option maxHeartbeats 500000 in
-- Three seam cases elaborate trace maps whose target measure depends on the boundary arc.
lemma weakPhaseCopies_seam (k m : ℕ) [NeZero m] (c : ℂ) (hc : c ^ m = 1)
    (p : slitTraceDomain k c) (n : ZMod (2 * m)) :
    arcTrace (seamBoundary k m n) (weakPhaseCopies m c p.val n) =
      arcTrace (seamBoundary k m n) (weakPhaseCopies m c p.val (n + 1)) := by
  let : NeZero (2 * m) := ⟨by have := NeZero.ne m; omega⟩
  let : Fact (1 < 2 * m) := ⟨by have := NeZero.ne m; omega⟩
  obtain ⟨hp1, hp0⟩ := (mem_slitTraceDomain k c p.val).mp p.property
  have hlt := ZMod.val_lt n
  have hs : seamBoundary k m n = boundaryArc k ((n + 1).val % 2) := by
    rw [seamBoundary_eq_boundaryArc, Twisted.parity_val]
  have hval : (n + 1).val = (n.val + 1) % (2 * m) := by
    rw [ZMod.val_add, ZMod.val_one]
  rw [hs]
  unfold weakPhaseCopies
  rcases Nat.even_or_odd' n.val with ⟨j, hj | hj⟩
  · have hn : (n + 1).val = n.val + 1 := by
      rw [hval]; exact Nat.mod_eq_of_lt (by omega)
    have hr : n.val % 2 = 0 := by omega
    have hq : n.val / 2 = j := by omega
    have hr' : (n.val + 1) % 2 = 1 := by omega
    have hq' : (n.val + 1) / 2 = j := by omega
    rw [hn, hr']
    simp only [hr, hq, hq', ite_true, one_ne_zero, ite_false, map_smul]
    rw [hp1]
  · have hr : n.val % 2 = 1 := by omega
    have hq : n.val / 2 = j := by omega
    by_cases hwrap : n.val + 1 < 2 * m
    · have hn : (n + 1).val = n.val + 1 := by rw [hval, Nat.mod_eq_of_lt hwrap]
      have hr' : (n.val + 1) % 2 = 0 := by omega
      have hq' : (n.val + 1) / 2 = j + 1 := by omega
      rw [hn, hr']
      simp only [hr, hq, hq', ite_true, one_ne_zero, ite_false, map_smul]
      rw [hp0, smul_smul, pow_succ]
    · have hn : (n + 1).val = 0 := by
        rw [hval, show n.val + 1 = 2 * m by omega, Nat.mod_self]
      have hjm : j + 1 = m := by omega
      rw [hn]
      simp only [hr, hq, Nat.zero_mod, Nat.zero_div, pow_zero,
        ite_true, one_ne_zero, ite_false, map_smul, one_smul]
      rw [hp0, smul_smul, ← pow_succ, hjm, hc, one_smul]

def reconstructWeakPhase (k m : ℕ) [NeZero m] (c : ℂ) (hc : c ^ m = 1)
    (p : slitTraceDomain k c) : weakDiskChain k m :=
  ⟨weakPhaseCopies m c p.val, (mem_weakDiskChain k m _).mpr
    (weakPhaseCopies_seam k m c hc p)⟩

end KsIndex.Trace
