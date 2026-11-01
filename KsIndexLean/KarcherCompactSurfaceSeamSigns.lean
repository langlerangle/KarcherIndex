module

public import KsIndexLean.KarcherCompactSurfaceEdges

@[expose] public section


/-! Alternating seam signs along the finite boundary subdivision. -/
noncomputable section
open Set Topology
namespace KsIndex.KarcherData.DiskCompactification
variable {k : ℕ} [h : Fact (2 ≤ k)]

omit h in
/-- The real part of the Gauss power along an arc has its expected alternating sign. -/
lemma edgeParameter_power_re (t : ℕ) (s : EdgeInterval k (t : ℤ)) :
    ((edgeParameter (t : ℤ) s).val ^ k).re =
      (-1 : ℝ) ^ (t + 1) * Real.cos (k * s.val - (t + 1) * Real.pi) := by
  change ((Circle.exp s.val : ℂ) ^ k).re = _
  rw [Circle.coe_exp, ← Complex.exp_nat_mul]
  have he : (k : ℂ) * ((s.val : ℂ) * Complex.I) = ((k * s.val : ℝ) : ℂ) * Complex.I := by
    push_cast
    ring
  rw [he, Complex.exp_mul_I]
  simp only [← Complex.ofReal_cos, ← Complex.ofReal_sin, Complex.add_re,
    Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re,
    Complex.I_im, mul_zero, zero_mul, sub_zero, add_zero]
  have hc := Real.cos_add_nat_mul_pi (k * s.val - (t + 1) * Real.pi) (t + 1)
  push_cast at hc
  convert hc using 1
  congr 1
  ring

lemma edgeParameter_centered_cos_pos (t : ℕ) (s : EdgeInterval k (t : ℤ))
    (hs : s.val ∈ Ioo (vertexAngle k (t : ℤ)) (vertexAngle k (t + 1 : ℤ))) :
    0 < Real.cos (k * s.val - (t + 1) * Real.pi) := by
  have hk : (0 : ℝ) < 2 * k := by have := h.out; positivity
  have hlo := (div_lt_iff₀ hk).mp hs.1
  have hhi := (lt_div_iff₀ hk).mp hs.2
  simp only [Int.cast_natCast, Int.cast_add, Int.cast_one] at hlo hhi
  apply Real.cos_pos_of_mem_Ioo
  constructor <;> nlinarith

/-- Arc number `t` belongs to precisely the parity-`t` seam family. -/
lemma edgeParameter_mem_arc (t : ℕ) (s : EdgeInterval k (t : ℤ))
    (hs : s.val ∈ Ioo (vertexAngle k (t : ℤ)) (vertexAngle k (t + 1 : ℤ))) :
    (edgeParameter (t : ℤ) s).val ∈ Surface.arc k t := by
  constructor
  · change ‖(Circle.exp s.val : ℂ)‖ = 1
    simp
  · rw [edgeParameter_power_re]
    have hp := edgeParameter_centered_cos_pos t s hs
    have he : (-1 : ℝ) ^ t * (-1 : ℝ) ^ (t + 1) = -1 := by
      rw [pow_succ, ← mul_assoc, ← pow_add, ← two_mul, pow_mul]
      simp
    rw [← mul_assoc, he, neg_one_mul]
    linarith

lemma edgeParameter_mem_arc_iff (t n : ℕ) (s : EdgeInterval k (t : ℤ))
    (hs : s.val ∈ Ioo (vertexAngle k (t : ℤ)) (vertexAngle k (t + 1 : ℤ))) :
    (edgeParameter (t : ℤ) s).val ∈ Surface.arc k n ↔ n % 2 = t % 2 := by
  have hp := (edgeParameter_mem_arc t s hs).2
  have hw := (edgeParameter_mem_arc t s hs).1
  change _ = 1 ∧ (-1 : ℝ) ^ n * _ < 0 ↔ _
  simp only [hw, eq_self, true_and]
  rw [neg_one_pow_eq_pow_mod_two n]
  rw [neg_one_pow_eq_pow_mod_two t] at hp
  have hn : n % 2 = 0 ∨ n % 2 = 1 := by omega
  have ht : t % 2 = 0 ∨ t % 2 = 1 := by omega
  rcases hn with hn | hn <;> rcases ht with ht | ht <;>
    simp_all only [pow_zero, pow_one, one_mul, neg_one_mul, zero_ne_one, one_ne_zero,
      iff_false, not_lt] <;> linarith

/-- The seam family is read directly from the parity of the angular interval. -/
lemma edgeParameter_mem_seamArc_iff {m : ℕ} [NeZero m]
    (i : ZMod (2 * m)) (t : ℕ) (s : EdgeInterval k (t : ℤ))
    (hs : s.val ∈ Ioo (vertexAngle k (t : ℤ)) (vertexAngle k (t + 1 : ℤ))) :
    (edgeParameter (t : ℤ) s).val ∈ Surface.seamArc k m i ↔
      (Surface.parity m (i + 1)).val = t % 2 := by
  rw [Surface.seamArc, edgeParameter_mem_arc_iff t _ s hs,
    Nat.mod_eq_of_lt (ZMod.val_lt _)]

/-- Exact cross-face pairing for an interior point of an angular arc. -/
lemma faceEdgeMap_eq_iff_parity {m : ℕ} [NeZero m]
    {i j : ZMod (2 * m)} (hij : i ≠ j) (t : ℕ) (s : EdgeInterval k (t : ℤ))
    (hs : s.val ∈ Ioo (vertexAngle k (t : ℤ)) (vertexAngle k (t + 1 : ℤ))) :
    faceEdgeMap (k := k) i (t : ℤ) s = faceEdgeMap j (t : ℤ) s ↔
      (j = i + 1 ∧ (Surface.parity m (i + 1)).val = t % 2) ∨
      (i = j + 1 ∧ (Surface.parity m (j + 1)).val = t % 2) := by
  rw [faceEdgeMap_eq_iff_interior hij (t : ℤ) s hs,
    edgeParameter_mem_seamArc_iff i t s hs, edgeParameter_mem_seamArc_iff j t s hs]

open PaperHalfPeriodRealization in
/-- Odd-numbered arcs of an even face are paired with the following odd face. -/
lemma faceEdgeMap_even_odd {m : ℕ} [NeZero m] (j : ZMod m)
    (t : ℕ) (s : EdgeInterval k (t : ℤ))
    (hs : s.val ∈ Ioo (vertexAngle k (t : ℤ)) (vertexAngle k (t + 1 : ℤ)))
    (ht : t % 2 = 1) :
    faceEdgeMap (k := k) (evenCopyIndex j) (t : ℤ) s =
      faceEdgeMap (oddCopyIndex j) (t : ℤ) s := by
  apply Quotient.sound
  refine ⟨rfl, Or.inr (Or.inr (Or.inl ⟨(evenCopyIndex_succ j).symm, ?_⟩))⟩
  rw [seamArc_evenCopyIndex]
  exact (edgeParameter_mem_arc_iff t 1 s hs).mpr (by simpa using ht.symm)

open PaperHalfPeriodRealization in
/-- Even-numbered arcs of an odd face are paired with the following even face. -/
lemma faceEdgeMap_odd_even {m : ℕ} [NeZero m] (j : ZMod m)
    (t : ℕ) (s : EdgeInterval k (t : ℤ))
    (hs : s.val ∈ Ioo (vertexAngle k (t : ℤ)) (vertexAngle k (t + 1 : ℤ)))
    (ht : t % 2 = 0) :
    faceEdgeMap (k := k) (oddCopyIndex j) (t : ℤ) s =
      faceEdgeMap (evenCopyIndex (j + 1)) (t : ℤ) s := by
  apply Quotient.sound
  refine ⟨rfl, Or.inr (Or.inr (Or.inl ⟨(oddCopyIndex_succ j).symm, ?_⟩))⟩
  rw [seamArc_oddCopyIndex]
  exact (edgeParameter_mem_arc_iff t 0 s hs).mpr (by simpa using ht.symm)

end KsIndex.KarcherData.DiskCompactification
