module

public import KsIndexLean.ChainPhaseReconstruction

@[expose] public section


open Set MeasureTheory
noncomputable section
namespace KsIndex.Trace
open KsIndex.WeakH1

/-- Complex-valued version of the original even/odd copy-counting identity. -/
lemma sum_zmod_mod_two_complex (m : ℕ) [NeZero m] (f : ℕ → ℂ) :
    ∑ n : ZMod (2 * m), f (n.val % 2) = (m : ℂ) * (f 0 + f 1) := by
  let : NeZero (2 * m) := ⟨by have := NeZero.ne m; omega⟩
  have hsum : ∑ n : ZMod (2 * m), f (n.val % 2) =
      ∑ i ∈ Finset.range (2 * m), f (i % 2) := by
    symm
    refine Finset.sum_bij' (fun i _ => (i : ZMod (2 * m))) (fun n _ => n.val) ?_ ?_ ?_ ?_ ?_
    · intros; exact Finset.mem_univ _
    · intro n _; exact Finset.mem_range.mpr (ZMod.val_lt n)
    · intro i hi; exact ZMod.val_cast_of_lt (Finset.mem_range.mp hi)
    · intro n _; exact ZMod.natCast_zmod_val n
    · intro i hi; rw [ZMod.val_cast_of_lt (Finset.mem_range.mp hi)]
  rw [hsum]
  clear hsum this
  induction m with
  | zero => simp
  | succ m ih =>
    rw [show 2 * (m + 1) = 2 * m + 1 + 1 by ring,
      Finset.sum_range_succ, Finset.sum_range_succ, ih, Nat.mul_mod_right,
      show (2 * m + 1) % 2 = 1 by omega]
    push_cast
    ring

lemma dirichlet_unit_smul (c : ℂ) (hc : ‖c‖ = 1) (u v : ComplexH1) :
    dirichlet (c • u) (c • v) = dirichlet u v := by
  rw [dirichlet_smul_left, dirichlet_smul_right, ← mul_assoc, Complex.conj_mul', hc]
  simp

lemma weakJacobi_unit_smul (V : BoundedRealPotential) (c : ℂ) (hc : ‖c‖ = 1)
    (u v : ComplexH1) : weakJacobi V (c • u) (c • v) = weakJacobi V u v := by
  rw [weakJacobi_smul_left, weakJacobi_smul_right, ← mul_assoc, Complex.conj_mul', hc]
  simp

lemma sum_weakPhaseCopies_form (m : ℕ) [NeZero m] (c : ℂ) (hc : c ^ m = 1)
    (B : ComplexH1 → ComplexH1 → ℂ)
    (hB : ∀ a : ℂ, ‖a‖ = 1 → ∀ u v, B (a • u) (a • v) = B u v)
    (p r : ComplexH1 × ComplexH1) :
    (∑ n : ZMod (2 * m), B (weakPhaseCopies m c p n) (weakPhaseCopies m c r n)) =
      (m : ℂ) * (B p.1 r.1 + B p.2 r.2) := by
  have hn := Complex.norm_eq_one_of_pow_eq_one hc (NeZero.ne m)
  calc
    _ = ∑ n : ZMod (2 * m), if n.val % 2 = 0 then B p.2 r.2 else B p.1 r.1 := by
      apply Finset.sum_congr rfl
      intro n _
      rw [weakPhaseCopies, weakPhaseCopies, hB _ (by rw [norm_pow, hn, one_pow])]
      split_ifs <;> rfl
    _ = _ := by
      have h := sum_zmod_mod_two_complex m
        (fun j => if j = 0 then B p.2 r.2 else B p.1 r.1)
      simpa only [ite_true, one_ne_zero, ite_false, add_comm] using h

end KsIndex.Trace
