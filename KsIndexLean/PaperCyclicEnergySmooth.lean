module

public import KsIndexLean.PaperPairCyclic
public import KsIndexLean.JacobiFields

@[expose] public section


noncomputable section
open Set MeasureTheory
namespace KsIndex.PaperSlitTransport
open KsIndex.Trace KsIndex.Surface KsIndex.SurfaceForm KsIndex.Twisted

lemma SmoothSlitPair.cyclic_seamVal {c : ℂ} (p : SmoothSlitPair c)
    {m : ℕ} [NeZero m] (hc : c ^ m = 1) : SeamVal 3 (p.cyclic m) := by
  have : NeZero (2 * m) := ⟨by have := NeZero.ne m; omega⟩
  have : Fact (1 < 2 * m) := ⟨by have := NeZero.ne m; omega⟩
  have h10 : (1 : ZMod (2 * 1)) ≠ 0 := by decide
  intro n z hz
  have hlt := ZMod.val_lt n
  have hv : (n + 1).val = (n.val + 1) % (2 * m) := by rw [ZMod.val_add, ZMod.val_one]
  rw [seamArc_eq] at hz
  change c ^ ((n + 1).val / 2) * smoothPairCopies p.upper p.lower
    (((n + 1).val % 2 : ℕ) : ZMod (2 * 1)) z =
    c ^ (n.val / 2) * smoothPairCopies p.upper p.lower ((n.val % 2 : ℕ) : ZMod (2 * 1)) z
  rcases Nat.even_or_odd' n.val with ⟨q, hq | hq⟩
  · have hnext : (n + 1).val = n.val + 1 := by rw [hv]; exact Nat.mod_eq_of_lt (by omega)
    have hr0 : n.val % 2 = 0 := by omega
    have hq0 : n.val / 2 = q := by omega
    have hq1 : (n.val + 1) / 2 = q := by omega
    have hr1 : (n.val + 1) % 2 = 1 := by omega
    rw [hnext, hr1] at hz
    simp only [hnext, hr0, hq0, hq1, hr1, Nat.cast_zero, Nat.cast_one,
      p.copies_eq, ite_true, ite_eq_right h10]
    rw [p.seam1_value z hz]
  · have hr1 : n.val % 2 = 1 := by omega
    have hq0 : n.val / 2 = q := by omega
    by_cases hwrap : n.val + 1 < 2 * m
    · have hnext : (n + 1).val = n.val + 1 := by rw [hv]; exact Nat.mod_eq_of_lt hwrap
      have hq1 : (n.val + 1) / 2 = q + 1 := by omega
      have hr0 : (n.val + 1) % 2 = 0 := by omega
      rw [hnext, hr0] at hz
      simp only [hnext, hr1, hq0, hq1, hr0, Nat.cast_zero, Nat.cast_one,
        p.copies_eq, ite_true, ite_eq_right h10]
      rw [p.seam0_value z hz, pow_succ]
      ring
    · have hnext : (n + 1).val = 0 := by
        rw [hv, show n.val + 1 = 2 * m by omega, Nat.mod_self]
      have hqm : q + 1 = m := by omega
      rw [hnext] at hz
      simp only [Nat.zero_mod] at hz
      simp only [hnext, hr1, hq0, Nat.zero_div, Nat.zero_mod, Nat.cast_zero, Nat.cast_one,
        pow_zero, one_mul, p.copies_eq, ite_true, ite_eq_right h10]
      rw [p.seam0_value z hz, ← mul_assoc, ← pow_succ, hqm, hc, one_mul]

/-- The cyclic field belongs to `EnergySmooth`, including both representative
normalizations, with no compact-support assumption. -/
theorem SmoothSlitPair.cyclic_mem_energySmooth {c : ℂ} (p : SmoothSlitPair c)
    {m : ℕ} [NeZero m] (hc : c ^ m = 1) :
    p.cyclic m ∈ KsIndex.FaithfulInjection.EnergySmooth 3 m :=
  ⟨p.cyclic_smooth hc, p.cyclic_energy m, p.cyclic_mass m,
    p.cyclic_punctureZero m, p.cyclic_seamVal hc⟩

/-- The flat equation converts to the metric Jacobi equation on every copy. -/
theorem SmoothSlitPair.cyclic_isJacobiField {c : ℂ} (p : SmoothSlitPair c)
    (m : ℕ) : IsJacobiField 3 m (p.cyclic m) := by
  intro n z hz
  exact KsIndex.JacobiFields.laplacianG_add_absASq_of_flat (by norm_num) hz
    (p.cyclic_flat_pde m n hz)

end KsIndex.PaperSlitTransport
