module

/-
KsIndexLean — The pure-Neumann seam lower bound, class by class.

For `k ≥ 3` and every rotation class `r < k`, the file proves
`neumannCount k (r : ZMod k) ≤ formIndex (Qd k) (NatCc k true true ⊓ Erot1 k r)`.

The negative test functions are truncated puncture-cutoff Jacobi modes:
`modeU k (k-r)` contributes when `2 ≤ r`, and the complex conjugate of
`modeU k r` contributes when `1 ≤ r ≤ k-2`. Their polynomial angular
factors are `w^(k-r)` and `conj(w)^r`; each mode also has a radial profile.
A common cutoff scale preserves negativity. When both modes occur,
`Bd_cm_cmC` makes their cross term zero, so their Gram matrix is diagonal
with negative entries and `formIndex_ge_of_neg` counts them.

For `r = 0`, this theorem gives only the zero lower bound because
`neumannCount k 0 = 0`. It does not supply the additional degree-zero
negative direction needed for the full class-zero seam count.
-/
public import KsIndexLean.SeamLowerConj
public import KsIndexLean.NeumannCount

@[expose] public section


noncomputable section

open Complex MeasureTheory Filter Topology
open scoped ContDiff

namespace KsIndex.SingleDisk

open KsIndex.Surface KsIndex.SurfaceForm KsIndex.SurfaceSym KsIndex.FormIndex KsIndex.Bracket
  KsIndex.SingleDiskBridge KsIndex.PunctureCutoff KsIndex.JacobiMode KsIndex.CutoffContinuity
  KsIndex.ModeDiag KsIndex.ThetaOrtho KsIndex.GradOrtho

variable {k : ℕ}

/-- The DtN symbol is negative on `1 ≤ ℓ ≤ k − 2`. -/
lemma sigma_neg_of_le (hk : 2 ≤ k) {ℓ : ℕ} (h1 : 1 ≤ ℓ) (h2 : ℓ ≤ k - 2) :
    KsIndex.Radial.sigma k ℓ < 0 := by
  unfold KsIndex.Radial.sigma KsIndex.Radial.kap
  have hℓ : (1 : ℝ) ≤ ℓ := by exact_mod_cast h1
  have hℓk : (ℓ : ℝ) + 2 ≤ k := by
    have : ℓ + 2 ≤ k := by omega
    exact_mod_cast this
  apply div_neg_of_neg_of_pos _ (by linarith)
  nlinarith

/-- A common cutoff scale making two cut-off Jacobi modes negative. -/
lemma exists_eps_cm_neg (hk : 2 ≤ k) {ℓ ℓ' : ℕ} (h1 : 1 ≤ ℓ) (h2 : ℓ ≤ k - 2) (h1' : 1 ≤ ℓ')
    (h2' : ℓ' ≤ k - 2) :
    ∃ ε : ℝ, 0 < ε ∧ ε < 1 ∧ Qd k (cm k ε ℓ) < 0 ∧ Qd k (cm k ε ℓ') < 0 := by
  have key : ∀ m : ℕ, 1 ≤ m → m ≤ k - 2 → ∀ᶠ ε : ℝ in 𝓝[>] (0:ℝ),
      0 < ε ∧ ε < 1 ∧ Qd k (cm k ε m) < 0 := by
    intro m hm1 hm2
    have h := eventually_eps_neg hk {m} (fun _ h => by rw [Finset.mem_singleton] at h; omega)
      (fun _ h => by rw [Finset.mem_singleton] at h; subst h; exact sigma_neg_of_le hk hm1 hm2)
    filter_upwards [h] with ε ⟨h0, h1, hneg⟩
    refine ⟨h0, h1, ?_⟩
    have := hneg (fun _ => 1) ⟨m, Finset.mem_singleton_self m, one_ne_zero⟩
    simpa [cm] using this
  obtain ⟨ε, ⟨h0, h1, hA⟩, ⟨_, _, hB⟩⟩ := ((key ℓ h1 h2).and (key ℓ' h1' h2')).exists
  exact ⟨ε, h0, h1, hA, hB⟩

/-- `Qd` of a scalar multiple, on a disk-smooth function. -/
lemma Qd_smul {f : ℂ → ℂ} (hk : 2 ≤ k) (hf : ContDiffOn ℝ ∞ f disk) (c : ℂ) :
    Qd k (c • f) = ‖c‖ ^ 2 * Qd k f := by
  have h := Bd_self_eq_Qd (k := k) hk (c • f)
  rw [Bd_const_smul_left hf, Bd_const_smul_right hf, Bd_self_eq_Qd hk, ← mul_assoc,
    Complex.conj_mul', ← Complex.ofReal_pow, ← Complex.ofReal_mul] at h
  exact_mod_cast h.symm

/-- The two-mode Gram computation: for `ℓ + ℓ' = k` and any coefficients,
`Qd(c₀ · truncCut ℓ + c₁ · truncCutC ℓ') = |c₀|² Qd(cm ℓ) + |c₁|² Qd(cm ℓ')`. -/
lemma Qd_pair (hk : 2 ≤ k) {ε : ℝ} (h0 : 0 < ε) (h1 : ε < 1) {ℓ ℓ' : ℕ} (hsum : ℓ + ℓ' = k)
    (c : Fin 2 → ℂ) :
    Qd k (∑ i, c i • ![truncCut k ε ℓ, truncCutC k ε ℓ'] i)
      = ‖c 0‖ ^ 2 * Qd k (cm k ε ℓ) + ‖c 1‖ ^ 2 * Qd k (cm k ε ℓ') := by
  have hk1 : 1 ≤ k := by omega
  set u : Fin 2 → ℂ → ℂ := ![cm k ε ℓ, cmC k ε ℓ'] with hu
  have hnice : ∀ i, DiskNice (u i) := by
    intro i; fin_cases i
    · exact diskNice_cm hk1 h0 h1 ℓ
    · exact diskNice_cmC hk1 h0 h1 ℓ'
  have hcongr : Qd k (∑ i, c i • ![truncCut k ε ℓ, truncCutC k ε ℓ'] i)
      = Qd k (fun w => ∑ i, c i • u i w) := by
    refine Qd_congr_disk fun w hw => ?_
    simp only [Finset.sum_apply, Pi.smul_apply, Fin.sum_univ_two, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.head_cons, hu, truncCut_eq_of_mem hw, truncCutC_eq_of_mem hw, cm]
  have hB := Bd_finsum (k := k) hk c c hnice
  rw [Bd_self_eq_Qd hk] at hB
  have hcross : Bd k (u 0) (u 1) = 0 := by
    simp only [hu, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
    exact Bd_cm_cmC hk h0 h1 hsum
  have hcross' : Bd k (u 1) (u 0) = 0 := by
    rw [← Bd_conj_symm, hcross, map_zero]
  have hd0 : Bd k (u 0) (u 0) = (Qd k (cm k ε ℓ) : ℂ) := by
    simp only [hu, Matrix.cons_val_zero]; exact Bd_self_eq_Qd hk _
  have hd1 : Bd k (u 1) (u 1) = (Qd k (cm k ε ℓ') : ℂ) := by
    change Bd k (cmC k ε ℓ') (cmC k ε ℓ') = _
    rw [Bd_self_eq_Qd hk, cmC, Qd_conjF]
  rw [hcongr]
  have hB' : (Qd k (fun w => ∑ i, c i • u i w) : ℂ)
      = ((‖c 0‖ ^ 2 * Qd k (cm k ε ℓ) + ‖c 1‖ ^ 2 * Qd k (cm k ε ℓ') : ℝ) : ℂ) := by
    rw [hB]
    simp only [Fin.sum_univ_two, hcross, hcross', hd0, hd1, mul_zero, add_zero, zero_add]
    rw [Complex.conj_mul', Complex.conj_mul']
    push_cast
    ring
  exact_mod_cast hB'

/-- **The pure-Neumann seam lower bound, class `r`** (`k ≥ 3`, `r < k`):
`neumannCount k r ≤ ind(Qd k) on NatCc k true true ⊓ Erot1 k r`. -/
theorem neumannCount_le_seamNat (hk : 3 ≤ k) {r : ℕ} (hr : r < k) :
    neumannCount k (r : ZMod k) ≤ formIndex (Qd k) (NatCc k true true ⊓ Erot1 k r) := by
  have hk2 : 2 ≤ k := by omega
  have hk1 : 1 ≤ k := by omega
  rw [neumannCount_eq hk, ZMod.val_natCast, Nat.mod_eq_of_lt hr]
  -- the Gram-diagonal negativity, packaged
  have hQ0 : Qd k (0 : ℂ → ℂ) = 0 := Qd_zero k
  rcases Nat.lt_or_ge r 1 with hr0 | hr1
  · -- class 0: nothing to show
    have : r = 0 := by omega
    subst this; simp
  rcases Nat.lt_or_ge r 2 with hr1' | hr2
  · -- r = 1: only the conjugate degree-one Jacobi mode
    have hr1 : r = 1 := by omega
    subst hr1
    have hle : (1 : ℕ) ≤ k - 2 := by omega
    obtain ⟨ε, h0, h1, hA, -⟩ := exists_eps_cm_neg hk2 le_rfl hle le_rfl hle
    have hcount : ((if 1 ≤ 1 ∧ 1 ≤ k - 2 then 1 else 0) + (if 2 ≤ 1 then 1 else 0) : ℕ) = 1 := by
      simp [hle]
    rw [hcount]
    refine formIndex_ge_of_neg hQ0 ![truncCutC k ε 1] (fun i => ?_) (fun c hc => ?_)
    · fin_cases i
      exact Submodule.mem_inf.mpr ⟨truncCutC_mem_NatCc hk1 h0 h1 1,
        truncCutC_mem_Erot1 hk1 ε (Nat.ModEq.refl 1)⟩
    · have hc0 : c 0 ≠ 0 := fun h => hc (funext fun i => by fin_cases i; exact h)
      have hsm : ContDiffOn ℝ ∞ (truncCutC k ε 1) disk := (truncCutC_mem_NatCc hk1 h0 h1 1).1
      simp only [Fin.sum_univ_one, Matrix.cons_val_zero]
      rw [Qd_smul hk2 hsm, Qd_congr_disk fun w hw => truncCutC_eq_of_mem hw, cmC, Qd_conjF]
      exact mul_neg_of_pos_of_neg (by positivity) hA
  rcases Nat.lt_or_ge r (k - 1) with hrk | hrk
  · -- 2 ≤ r ≤ k − 2: both modes
    have hℓ1 : 1 ≤ k - r := by omega
    have hℓ2 : k - r ≤ k - 2 := by omega
    have hr2' : r ≤ k - 2 := by omega
    obtain ⟨ε, h0, h1, hA, hB⟩ := exists_eps_cm_neg hk2 hℓ1 hℓ2 hr1 hr2'
    have hcount : ((if 1 ≤ r ∧ r ≤ k - 2 then 1 else 0) + (if 2 ≤ r then 1 else 0) : ℕ) = 2 := by
      simp [hr1, hr2', hr2]
    rw [hcount]
    have hsum : (k - r) + r = k := by omega
    refine formIndex_ge_of_neg hQ0 ![truncCut k ε (k - r), truncCutC k ε r] (fun i => ?_)
      (fun c hc => ?_)
    · fin_cases i
      · exact Submodule.mem_inf.mpr ⟨truncCut_mem_NatCc hk1 h0 h1 _,
          truncCut_mem_Erot1 hk1 ε ⟨1, by omega⟩⟩
      · exact Submodule.mem_inf.mpr ⟨truncCutC_mem_NatCc hk1 h0 h1 _,
          truncCutC_mem_Erot1 hk1 ε (Nat.ModEq.refl r)⟩
    · rw [Qd_pair hk2 h0 h1 hsum c]
      have hc' : c 0 ≠ 0 ∨ c 1 ≠ 0 := by
        by_contra hcon
        push_neg at hcon
        exact hc (funext fun i => by fin_cases i <;> simp [hcon.1, hcon.2])
      have hA' : ‖c 0‖ ^ 2 * Qd k (cm k ε (k - r)) ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos (by positivity) hA.le
      have hB' : ‖c 1‖ ^ 2 * Qd k (cm k ε r) ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos (by positivity) hB.le
      rcases hc' with hc0 | hc1
      · have : ‖c 0‖ ^ 2 * Qd k (cm k ε (k - r)) < 0 :=
          mul_neg_of_pos_of_neg (by positivity) hA
        linarith
      · have : ‖c 1‖ ^ 2 * Qd k (cm k ε r) < 0 :=
          mul_neg_of_pos_of_neg (by positivity) hB
        linarith
  · -- r = k − 1: only the degree-one Jacobi mode
    have hrk1 : r = k - 1 := by omega
    have hle : (1 : ℕ) ≤ k - 2 := by omega
    obtain ⟨ε, h0, h1, hA, -⟩ := exists_eps_cm_neg hk2 le_rfl hle le_rfl hle
    have hcount : ((if 1 ≤ r ∧ r ≤ k - 2 then 1 else 0) + (if 2 ≤ r then 1 else 0) : ℕ) = 1 := by
      have : ¬ (r ≤ k - 2) := by omega
      simp [this, hr2]
    rw [hcount]
    refine formIndex_ge_of_neg hQ0 ![truncCut k ε 1] (fun i => ?_) (fun c hc => ?_)
    · fin_cases i
      exact Submodule.mem_inf.mpr ⟨truncCut_mem_NatCc hk1 h0 h1 1,
        truncCut_mem_Erot1 hk1 ε ⟨1, by omega⟩⟩
    · have hc0 : c 0 ≠ 0 := fun h => hc (funext fun i => by fin_cases i; exact h)
      have hsm : ContDiffOn ℝ ∞ (truncCut k ε 1) disk := (truncCut_mem_NatCc hk1 h0 h1 1).1
      simp only [Fin.sum_univ_one, Matrix.cons_val_zero]
      rw [Qd_smul hk2 hsm, Qd_congr_disk fun w hw => truncCut_eq_of_mem hw]
      exact mul_neg_of_pos_of_neg (by positivity) hA

end KsIndex.SingleDisk
