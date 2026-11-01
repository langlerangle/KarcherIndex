module

/-
# Single-valuedness across a seam

`Surface.SeamVal` requires `u (n+1) w = u n w` on `seamArc k m n`, so the two
chart representatives give the same value at an identified seam point.

This file considers a function supported at one point of copy `n₀`'s receiving
arc. For `m ≥ 1`, copies `n₀` and `n₀−1` are distinct. The function takes value
one on the receiving side and zero on the giving side of the same seam, violating
`SeamVal`. The theorem `arcSpike_not_mem` therefore excludes it from `BoundedJacobi`.

Unlike a deleted puncture, a seam point belongs to the surface. Its two chart
values must agree, rather than being independently assigned.
-/
public import KsIndexLean.Surface
public import KsIndexLean.PunctureSpike

@[expose] public section


noncomputable section

open Complex Real Set
open KsIndex.Surface KsIndex.PunctureSpike

namespace KsIndex.ArcSpike

variable {k m : ℕ}

/-- Off its copy, the spike vanishes everywhere. -/
lemma spike_eq_zero' {n₀ : ZMod (2 * m)} {p : ℂ} {n : ZMod (2 * m)} (hn : n ≠ n₀) (w : ℂ) :
    spike m n₀ p n w = 0 := by
  unfold spike
  rw [if_neg]
  exact fun h => hn h.1

/-- A point-supported function on copy `n₀`'s receiving arc is not in `BoundedJacobi`.
That arc is `seamArc k m (n₀ − 1)`, shared with copy `n₀ − 1`;
the function violates `SeamVal` there. -/
theorem arcSpike_not_mem (hm : 1 ≤ m) {n₀ : ZMod (2 * m)} {p : ℂ}
    (hparc : p ∈ arc k (parity m n₀).val) : spike m n₀ p ∉ BoundedJacobi k m := by
  intro hmem
  have hidx : n₀ - 1 + 1 = n₀ := by ring
  have hseam : p ∈ seamArc k m (n₀ - 1) := by
    show p ∈ arc k (parity m (n₀ - 1 + 1)).val
    rw [hidx]
    exact hparc
  have h := hmem.2.2.2.2 (n₀ - 1) p hseam
  rw [hidx, spike_self] at h
  have hne : n₀ - 1 ≠ n₀ := by
    intro he
    have h10 : (1 : ZMod (2 * m)) = 0 := sub_eq_self.mp he
    haveI : Fact (1 < 2 * m) := ⟨by omega⟩
    exact one_ne_zero h10
  rw [spike_eq_zero' hne p] at h
  exact one_ne_zero h

end KsIndex.ArcSpike
