module

/-
Finite mode sums with prescribed rotation character and negative disk energy.

The class-`r` coefficient vector transports to the disk: for `n ∈ [−N, N]` place the
coefficient `t n` on the mode of angular index `ℓ(n) = k·n + (k−r)`: use
`modeS k |ℓ(n)|` for nonnegative index and its conjugate for negative index.
For `k ≥ 3` and `1 ≤ r ≤ k−1`, these indices are nonzero. Divide by `|ℓ(n)|`
to normalize the boundary amplitude:

  `Psi k r N t = Σ_{|n| ≤ N} (t n/|ℓ(n)|)·fam(n)`.

* every pair of distinct modes has vanishing `Bd` (`Bd_fam_offdiag` — the uniform zpow
  character `rot1 a (fam n) = a^{ℓ(n)} • fam n` plus `exists_char`);
* the diagonal energies are `2π·ℓ(n)²·σ_k(|ℓ(n)|)` (`Qd_fam`), and `sigma_natAbs_eq` at
  residue `k−r` turns `σ_k(|ℓ(n)|)` into `k·σ_{(aOf r k; bOf k)}(n)`;
* hence (`Bd_finsum` + `Bd_self_eq_Qd`):

  `Qd_Psi_eq : Qd k (Psi k r N t) = 2π·k·NQformArc (aOf r k) (bOf k) (trunc N t)`

  — with `exists_trunc` and `exists_witness`, this is `< 0` for suitable `η, N`
  when `k ≥ 3` and `1 ≤ r ≤ k−1`;
* `Psi_mem_Erot1 : Psi k r N t ∈ Erot1 k r` (all modes carry the same `ζ^r` character under
  the `rotUnit` rotation), and `Psi` is globally `C^∞` (`contDiff_Psi`).

The witness here has no asserted Dirichlet-slit vanishing. Imposing that boundary
condition requires a separate cutoff argument.
-/
public import KsIndexLean.ModeKit
public import KsIndexLean.ArcTrunc
public import KsIndexLean.SymbolReindex

@[expose] public section


noncomputable section

open Real Set Complex
open scoped ContDiff
open KsIndex.Surface KsIndex.JacobiMode KsIndex.SingleDiskBridge KsIndex.Radial
  KsIndex.SingleDisk KsIndex.ModeDiag KsIndex.FormIndex KsIndex.ModeKit KsIndex.ArcForm
  KsIndex.ArcLower KsIndex.ArcTrunc KsIndex.Reindex KsIndex.SurfaceSym

namespace KsIndex.ModeWitness

variable {k r : ℕ}

/-! ### The class lattice and the mode family -/

/-- The angular index of slot `n`: `ℓ(n) = k·n + (k−r)`. -/
def lz (k r : ℕ) (n : ℤ) : ℤ := (k : ℤ) * n + ((k - r : ℕ) : ℤ)

lemma lz_ne_zero (hk : 3 ≤ k) (hr1 : 1 ≤ r) (hrk : r ≤ k - 1) (n : ℤ) : lz k r n ≠ 0 := by
  unfold lz
  intro h
  rcases le_or_gt 0 n with hn | hn
  · have h1 : (0:ℤ) ≤ (k:ℤ) * n := mul_nonneg (by omega) hn
    omega
  · have hn1 : n ≤ -1 := by omega
    have h1 : (k:ℤ) * n ≤ (k:ℤ) * (-1) := by
      exact mul_le_mul_of_nonneg_left hn1 (by omega)
    omega

lemma lz_injective (hk : 3 ≤ k) : Function.Injective (lz k r) := by
  intro m n h
  unfold lz at h
  have h2 : (k:ℤ) * m = (k:ℤ) * n := by omega
  exact mul_left_cancel₀ (Int.natCast_ne_zero.mpr (by omega)) h2

lemma one_le_natAbs_lz (hk : 3 ≤ k) (hr1 : 1 ≤ r) (hrk : r ≤ k - 1) (n : ℤ) :
    1 ≤ (lz k r n).natAbs := by
  have := lz_ne_zero hk hr1 hrk n
  omega

/-- The mode of slot `n`: `modeS k |ℓ(n)|` for `ℓ(n) ≥ 0`, its conjugate otherwise. -/
def fam (k r : ℕ) (n : ℤ) : ℂ → ℂ :=
  if 0 ≤ lz k r n then modeS k (lz k r n).natAbs else conjF (modeS k (lz k r n).natAbs)

lemma contDiff_fam (k r : ℕ) (n : ℤ) : ContDiff ℝ ∞ (fam k r n) := by
  unfold fam
  split
  · exact contDiff_modeS k _
  · exact contDiff_conjF (contDiff_modeS k _)

lemma diskNice_fam (k r : ℕ) (n : ℤ) : DiskNice (fam k r n) :=
  KsIndex.FormIndex.diskNice_of_contDiff (contDiff_fam k r n)

/-! ### The uniform zpow character -/

lemma conj_eq_inv {a : ℂ} (ha : ‖a‖ = 1) : (starRingEnd ℂ) a = a⁻¹ := by
  refine eq_inv_of_mul_eq_one_right ?_
  rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, ha]
  norm_num

lemma rot1_fam {a : ℂ} (ha : ‖a‖ = 1) (k r : ℕ) (n : ℤ) :
    rot1 a (fam k r n) = (a ^ (lz k r n)) • fam k r n := by
  have ha0 : a ≠ 0 := by
    intro h
    rw [h, norm_zero] at ha
    norm_num at ha
  unfold fam
  split
  · rename_i hpos
    have hz : a ^ (lz k r n) = a ^ ((lz k r n).natAbs) := by
      rw [← zpow_natCast a (lz k r n).natAbs]
      congr 1
      omega
    rw [hz]
    exact rot1_modeS ha k _
  · rename_i hneg
    have hz : a ^ (lz k r n) = (starRingEnd ℂ) (a ^ ((lz k r n).natAbs)) := by
      rw [conj_eq_inv (by rw [norm_pow, ha, one_pow]), ← zpow_natCast a, ← zpow_neg]
      congr 1
      omega
    rw [hz]
    exact rot1_conjF_modeS ha k _

/-! ### Off-diagonal vanishing -/

lemma Bd_fam_offdiag (hk : 3 ≤ k) {m n : ℤ} (hmn : m ≠ n) :
    Bd k (fam k r m) (fam k r n) = 0 := by
  have hΔ : lz k r n - lz k r m ≠ 0 := by
    intro h
    exact hmn (lz_injective hk (by omega : lz k r m = lz k r n))
  obtain ⟨a, ha, hchar⟩ := exists_char (lz k r n - lz k r m) hΔ
  have ha0 : a ≠ 0 := by
    intro h
    rw [h, norm_zero] at ha
    norm_num at ha
  refine Bd_eq_zero_of_equivariant ((contDiff_fam k r m).contDiffOn)
    ((contDiff_fam k r n).contDiffOn) ha (rot1_fam ha k r m) (rot1_fam ha k r n) ?_
  rw [conj_eq_inv (by rw [norm_zpow, ha, one_zpow]), ← zpow_neg, ← zpow_add₀ ha0,
    show -(lz k r m) + lz k r n = lz k r n - lz k r m by ring, hchar]
  norm_num

/-! ### The diagonal energies -/

lemma Qd_fam (hk : 3 ≤ k) (hr1 : 1 ≤ r) (hrk : r ≤ k - 1) (n : ℤ) :
    Qd k (fam k r n) = 2 * Real.pi
      * (((lz k r n).natAbs : ℝ) ^ 2 * sigma k (lz k r n).natAbs) := by
  have hk2 : 2 ≤ k := by omega
  have hℓ := one_le_natAbs_lz hk hr1 hrk n
  unfold fam
  split
  · exact Qd_modeS hk2 hℓ
  · exact Qd_conjF_modeS hk2 hℓ

/-! ### The witness -/

/-- The slot map `Fin (2N+1) → ℤ`, `i ↦ i − N`. -/
def slot (N : ℕ) (i : Fin (2 * N + 1)) : ℤ := (i : ℤ) - N

/-- The normalized coefficient of slot `n`. -/
def coefOf (k r : ℕ) (t : ℤ → ℂ) (n : ℤ) : ℂ := t n / ((lz k r n).natAbs : ℂ)

/-- **The finite mode-sum witness.** -/
def Psi (k r N : ℕ) (t : ℤ → ℂ) : ℂ → ℂ :=
  fun w => ∑ i : Fin (2 * N + 1), coefOf k r t (slot N i) • fam k r (slot N i) w

lemma slot_injective (N : ℕ) : Function.Injective (slot N) := by
  intro i j h
  unfold slot at h
  have : (i : ℤ) = (j : ℤ) := by omega
  exact Fin.ext (by exact_mod_cast this)

lemma contDiff_Psi (k r N : ℕ) (t : ℤ → ℂ) : ContDiff ℝ ∞ (Psi k r N t) := by
  unfold Psi
  apply ContDiff.sum
  intro i _
  exact (contDiff_fam k r (slot N i)).const_smul _

/-! ### The energy identity -/

/-- `Qd (Psi) = 2π·k·NQformArc (aOf r k) (bOf k) (trunc N t)`. -/
theorem Qd_Psi_eq (hk : 3 ≤ k) (hr1 : 1 ≤ r) (hrk : r ≤ k - 1) (N : ℕ) (t : ℤ → ℂ) :
    Qd k (Psi k r N t)
      = 2 * Real.pi * ((k : ℝ) * NQformArc (aOf r k) (bOf k) (trunc N t)) := by
  have hk2 : 2 ≤ k := by omega
  -- complexified energy via Bd_finsum
  have hBd : (Qd k (Psi k r N t) : ℂ)
      = ∑ i : Fin (2 * N + 1), ∑ j : Fin (2 * N + 1),
          (starRingEnd ℂ) (coefOf k r t (slot N i)) * coefOf k r t (slot N j)
            * Bd k (fam k r (slot N i)) (fam k r (slot N j)) := by
    rw [← Bd_self_eq_Qd hk2]
    exact Bd_finsum hk2 _ _ (fun i => diskNice_fam k r (slot N i))
  -- off-diagonals vanish; the double sum collapses to the diagonal
  have hdiag : (Qd k (Psi k r N t) : ℂ)
      = ∑ i : Fin (2 * N + 1),
          ((‖coefOf k r t (slot N i)‖ ^ 2 : ℝ) : ℂ) * (Qd k (fam k r (slot N i)) : ℂ) := by
    rw [hBd]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [Finset.sum_eq_single i (fun j _ hji => ?_) (fun h => absurd (Finset.mem_univ i) h)]
    · rw [Bd_self_eq_Qd hk2]
      congr 1
      rw [mul_comm ((starRingEnd ℂ) (coefOf k r t (slot N i))), Complex.mul_conj,
        Complex.normSq_eq_norm_sq]
    · rw [Bd_fam_offdiag hk (fun h => hji ((slot_injective N h).symm)), mul_zero]
  -- realify and evaluate termwise
  have hreal : Qd k (Psi k r N t)
      = ∑ i : Fin (2 * N + 1),
          ‖coefOf k r t (slot N i)‖ ^ 2 * Qd k (fam k r (slot N i)) := by
    have h2 : ((∑ i : Fin (2 * N + 1),
        ‖coefOf k r t (slot N i)‖ ^ 2 * Qd k (fam k r (slot N i)) : ℝ) : ℂ)
        = (Qd k (Psi k r N t) : ℂ) := by
      rw [hdiag]
      push_cast
      rfl
    exact_mod_cast h2.symm
  rw [hreal]
  -- termwise: ‖t/|ℓ|‖²·2π·|ℓ|²·σ_k(|ℓ|) = 2π·k·σArc(n)·‖t n‖²
  have hterm : ∀ i : Fin (2 * N + 1),
      ‖coefOf k r t (slot N i)‖ ^ 2 * Qd k (fam k r (slot N i))
        = 2 * Real.pi * ((k : ℝ)
            * (sigmaArc (aOf r k) (bOf k) (slot N i) * ‖t (slot N i)‖ ^ 2)) := by
    intro i
    set n := slot N i
    have hℓ1 := one_le_natAbs_lz hk hr1 hrk n
    have hℓR : (0:ℝ) < ((lz k r n).natAbs : ℝ) := by exact_mod_cast hℓ1
    have hσ : sigma k (lz k r n).natAbs
        = (k : ℝ) * sigmaArc (aOf r k) (bOf k) n := by
      have h := sigma_natAbs_eq (k := k) (r := k - r) (by omega) (by omega) (by omega) n
      rw [show k - (k - r) = r by omega] at h
      exact h
    rw [Qd_fam hk hr1 hrk n, coefOf, norm_div, div_pow, hσ]
    rw [Complex.norm_natCast]
    field_simp
  rw [Finset.sum_congr rfl (fun i _ => hterm i)]
  -- reindex Fin (2N+1) ↔ Icc (−N) N and match NQ_trunc_eq_sum
  rw [NQ_trunc_eq_sum]
  have hre : (∑ i : Fin (2 * N + 1),
      2 * Real.pi * ((k : ℝ)
        * (sigmaArc (aOf r k) (bOf k) (slot N i) * ‖t (slot N i)‖ ^ 2)))
      = 2 * Real.pi * ((k : ℝ)
        * ∑ ℓ ∈ Finset.Icc (-(N : ℤ)) N, sigmaArc (aOf r k) (bOf k) ℓ * ‖t ℓ‖ ^ 2) := by
    rw [Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_nbij' (i := slot N)
      (j := fun ℓ => ⟨min (ℓ + N).toNat (2 * N), by omega⟩)
      (fun i _ => ?_) (fun ℓ hℓ => Finset.mem_univ _) (fun i _ => ?_) (fun ℓ hℓ => ?_)
      (fun i _ => rfl)
    · rw [Finset.mem_Icc]
      unfold slot
      omega
    · unfold slot
      apply Fin.ext
      simp only []
      omega
    · rw [Finset.mem_Icc] at hℓ
      unfold slot
      simp only []
      omega
  rw [hre]

/-! ### Class membership and the negative witness -/

/-- Each mode is a `rotUnit`-eigenfunction with the class-`r` eigenvalue `ζ_k^r`. -/
lemma rot1_fam_rotUnit (hk : 3 ≤ k) (hr1 : 1 ≤ r) (hrk : r ≤ k - 1) (n : ℤ) :
    rot1 (rotUnit k : ℂ) (fam k r n) = (zeta k ^ r) • fam k r n := by
  have hk1 : 1 ≤ k := by omega
  rw [rot1_fam (Circle.norm_coe _) k r n]
  congr 1
  rw [rotUnit_coe_eq_zeta_inv, ← zpow_natCast (zeta k) r]
  rw [show ((zeta k)⁻¹ : ℂ) = zeta k ^ (-1 : ℤ) by rw [zpow_neg, zpow_one]]
  rw [← zpow_mul]
  have hzk : zeta k ^ (k : ℤ) = 1 := by
    rw [zpow_natCast, zeta_pow_N (by omega)]
  have hdvd : (k : ℤ) ∣ (-1 * lz k r n) - (r : ℤ) := by
    refine ⟨-(n + 1), ?_⟩
    unfold lz
    push_cast
    ring_nf
    omega
  obtain ⟨q, hq⟩ := hdvd
  rw [show -1 * lz k r n = (r : ℤ) + (k : ℤ) * q by linarith [hq], zpow_add₀
    (by rw [zeta]; exact Complex.exp_ne_zero _), zpow_mul, hzk, one_zpow, mul_one]

/-- **`Psi ∈ Erot1 k r`**. -/
theorem Psi_mem_Erot1 (hk : 3 ≤ k) (hr1 : 1 ≤ r) (hrk : r ≤ k - 1) (N : ℕ) (t : ℤ → ℂ) :
    Psi k r N t ∈ Erot1 k r := by
  rw [Erot1, Module.End.mem_eigenspace_iff]
  funext w
  show (Psi k r N t) ((rotUnit k : ℂ) * w) = zeta k ^ r • (Psi k r N t) w
  unfold Psi
  simp only [Finset.smul_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  have h := congrFun (rot1_fam_rotUnit hk hr1 hrk (slot N i)) w
  simp only [rot1_apply, Pi.smul_apply, smul_eq_mul] at h
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [h]
  ring

/-- **The negative-energy disk witness.**  For `k ≥ 3`, `1 ≤ r ≤ k−1`, there are
`η, N` with `Psi k r N (fc (psiF η))` a class-`r` smooth disk function of negative energy. -/
theorem exists_mode_witness (hk : 3 ≤ k) (hr1 : 1 ≤ r) (hrk : r ≤ k - 1) :
    ∃ (η : ℝ) (N : ℕ),
      Psi k r N (Parseval.fc (KsIndex.ArcField.psiF η)) ∈ Erot1 k r
        ∧ ContDiff ℝ ∞ (Psi k r N (Parseval.fc (KsIndex.ArcField.psiF η)))
        ∧ Qd k (Psi k r N (Parseval.fc (KsIndex.ArcField.psiF η))) < 0 := by
  have ha : aOf r k ∈ Set.Ioo (0:ℝ) 1 := aOf_mem hk hr1 hrk
  have hb : 2 * (aOf r k * (1 - aOf r k)) ≤ bOf k ^ 2 := two_mul_aOf_le hk hr1 hrk
  obtain ⟨η, hη0, hη14, hmem, hneg⟩ :=
    KsIndex.ArcWitness.exists_witness ha hb
  set t := Parseval.fc (KsIndex.ArcField.psiF η) with htdef
  obtain ⟨N, hNneg, -⟩ :=
    exists_trunc ha (bOf k) hmem.1 hneg 1 one_pos
  refine ⟨η, N, Psi_mem_Erot1 hk hr1 hrk N t, contDiff_Psi k r N t, ?_⟩
  rw [Qd_Psi_eq hk hr1 hrk N t]
  have hπk : (0:ℝ) < 2 * Real.pi * (k : ℝ) := by
    have : (0:ℝ) < (k:ℝ) := by exact_mod_cast (by omega : 0 < k)
    positivity
  calc 2 * Real.pi * ((k : ℝ) * NQformArc (aOf r k) (bOf k) (trunc N t))
      = (2 * Real.pi * (k : ℝ)) * NQformArc (aOf r k) (bOf k) (trunc N t) := by ring
    _ < 0 := mul_neg_of_pos_of_neg hπk hNneg

end KsIndex.ModeWitness
