module

/-
# Uniform disk bounds for finite mode witnesses

For `k ≥ 3`, `1 ≤ r ≤ k - 1` and `η > 0`, `Psi_disk_bounds` supplies
nonnegative constants bounding the value and the real Fréchet derivative
operator norm of `Psi k r N (fc (psiF η))` on the closed unit disk,
uniformly in the truncation index `N`.

The proof bounds each mode and its derivative using a compactness bound
`Cg` for the derivative of `groundR`. It then dominates finite sums by
the summable weighted coefficient masses
`∑' n, (|lz k r n| + κ) * ‖fc (psiF η) n‖` and
`∑' n, (|lz k r n| + κ + Cg) * ‖fc (psiF η) n‖`.
The estimate `|lz k r n| ≤ k * (|n| + 1)` reduces these to the Fourier
coefficient summability results in `ArcSmooth`.

Uniformity in `N` permits the truncation index to increase as a boundary
collar shrinks, without changing the disk bounds used in cutoff estimates.
-/
public import KsIndexLean.ModeWitness
public import KsIndexLean.ModeCorr
public import KsIndexLean.CutoffContinuity
public import KsIndexLean.SlitCutoffGrad
public import KsIndexLean.ArcSmooth

@[expose] public section


noncomputable section

open Real Set Complex Filter
open KsIndex.Surface KsIndex.SingleDisk KsIndex.Radial KsIndex.ModeKit KsIndex.ModeWitness
  KsIndex.CutoffContinuity KsIndex.ArcField

namespace KsIndex.ModeGrad

variable {k r : ℕ}

/-! ### Elementary fderiv bounds -/

/-- The real Fréchet derivative of `z ↦ z^p`. -/
lemma hasFDerivAt_pow_real (p : ℕ) (w : ℂ) :
    HasFDerivAt (fun z : ℂ => z ^ p)
      ((((1 : ℂ →L[ℂ] ℂ).smulRight ((p : ℂ) * w ^ (p - 1)))).restrictScalars ℝ) w :=
  ((hasDerivAt_pow p w).hasFDerivAt).restrictScalars ℝ

lemma norm_fderiv_pow_le (p : ℕ) {w : ℂ} (hw : ‖w‖ ≤ 1) :
    ‖fderiv ℝ (fun z : ℂ => z ^ p) w‖ ≤ p := by
  rw [(hasFDerivAt_pow_real p w).fderiv, ContinuousLinearMap.norm_restrictScalars,
    ContinuousLinearMap.norm_smulRight_apply, ContinuousLinearMap.one_def,
    ContinuousLinearMap.norm_id, one_mul, norm_mul, Complex.norm_natCast, norm_pow]
  calc (p : ℝ) * ‖w‖ ^ (p - 1) ≤ (p : ℝ) * 1 :=
        mul_le_mul_of_nonneg_left (pow_le_one₀ (norm_nonneg w) hw) (Nat.cast_nonneg p)
    _ = p := mul_one _

/-- A compactness bound for `∇groundR` on the closed disk. -/
lemma exists_groundR_fderiv_bound (k : ℕ) :
    ∃ Cg : ℝ, 0 ≤ Cg ∧ ∀ w : ℂ, ‖w‖ ≤ 1 → ‖fderiv ℝ (groundR k) w‖ ≤ Cg := by
  obtain ⟨C, hC⟩ := (isCompact_closedBall (0 : ℂ) 1).exists_bound_of_continuousOn
    (((contDiff_groundR k).continuous_fderiv (by simp)).continuousOn)
  refine ⟨max C 0, le_max_right _ _, fun w hw => ?_⟩
  refine le_trans (hC w ?_) (le_max_left _ _)
  rwa [Metric.mem_closedBall, dist_zero_right]

/-- `|groundR| ≤ κ` (globally). -/
lemma abs_groundR_le (hk2 : 2 ≤ k) (w : ℂ) : |groundR k w| ≤ kap k := by
  have h := abs_groundC_le hk2 w
  rwa [groundC, Complex.norm_real, Real.norm_eq_abs] at h

/-- **The mode gradient bound**: `‖∇(modeS k p)(w)‖ ≤ ((p+κ)·p + C_g)` on the closed disk. -/
lemma norm_fderiv_modeS_le (hk2 : 2 ≤ k) (p : ℕ) {Cg : ℝ}
    (hCg : ∀ w : ℂ, ‖w‖ ≤ 1 → ‖fderiv ℝ (groundR k) w‖ ≤ Cg)
    {w : ℂ} (hw : ‖w‖ ≤ 1) :
    ‖fderiv ℝ (modeS k p) w‖ ≤ ((p : ℝ) + kap k) * p + Cg := by
  have hgd : DifferentiableAt ℝ (fun w : ℂ => (p : ℝ) + groundR k w) w :=
    (differentiableAt_const _).add
      (((contDiff_groundR k).differentiable (by simp)).differentiableAt)
  have hfd : DifferentiableAt ℝ (fun z : ℂ => z ^ p) w :=
    (hasFDerivAt_pow_real p w).differentiableAt
  have hFD := hasFDerivAt_cutMul (c := fun w : ℂ => (p : ℝ) + groundR k w)
    (f := fun z : ℂ => z ^ p) hgd hfd
  have hmod : HasFDerivAt (modeS k p)
      ((((p : ℝ) + groundR k w : ℝ) : ℂ) • fderiv ℝ (fun z : ℂ => z ^ p) w
        + (w ^ p) • (Complex.ofRealCLM.comp
            (fderiv ℝ (fun w : ℂ => (p : ℝ) + groundR k w) w))) w := hFD
  rw [hmod.fderiv]
  have hgr := abs_groundR_le hk2 w
  have hκ0 : 0 ≤ kap k := (kap_pos hk2).le
  -- the scalar factors
  have hcw : ‖((((p : ℝ) + groundR k w : ℝ)) : ℂ)‖ ≤ (p : ℝ) + kap k := by
    rw [Complex.norm_real, Real.norm_eq_abs]
    calc |(p : ℝ) + groundR k w| ≤ |(p : ℝ)| + |groundR k w| := abs_add_le _ _
      _ ≤ (p : ℝ) + kap k := by
          rw [abs_of_nonneg (Nat.cast_nonneg p)]
          linarith
  have hwp : ‖w ^ p‖ ≤ 1 := by
    rw [norm_pow]
    exact pow_le_one₀ (norm_nonneg w) hw
  -- the composed cutoff derivative
  have hcomp : ‖Complex.ofRealCLM.comp
      (fderiv ℝ (fun w : ℂ => (p : ℝ) + groundR k w) w)‖ ≤ Cg := by
    rw [show fderiv ℝ (fun w : ℂ => (p : ℝ) + groundR k w) w = fderiv ℝ (groundR k) w from
      fderiv_const_add _]
    refine ContinuousLinearMap.opNorm_le_bound _
      (le_trans (norm_nonneg _) (hCg w hw)) (fun v => ?_)
    rw [ContinuousLinearMap.comp_apply, Complex.ofRealCLM_apply, Complex.norm_real,
      Real.norm_eq_abs, ← Real.norm_eq_abs]
    exact le_trans ((fderiv ℝ (groundR k) w).le_opNorm v)
      (mul_le_mul_of_nonneg_right (hCg w hw) (norm_nonneg v))
  calc ‖(((((p : ℝ) + groundR k w : ℝ)) : ℂ)) • fderiv ℝ (fun z : ℂ => z ^ p) w
        + (w ^ p) • (Complex.ofRealCLM.comp
            (fderiv ℝ (fun w : ℂ => (p : ℝ) + groundR k w) w))‖
      ≤ ‖((((p : ℝ) + groundR k w : ℝ)) : ℂ)‖ * ‖fderiv ℝ (fun z : ℂ => z ^ p) w‖
        + ‖w ^ p‖ * ‖Complex.ofRealCLM.comp
            (fderiv ℝ (fun w : ℂ => (p : ℝ) + groundR k w) w)‖ := by
        refine le_trans (norm_add_le _ _) ?_
        rw [norm_smul, norm_smul]
    _ ≤ ((p : ℝ) + kap k) * p + 1 * Cg := by
        refine add_le_add ?_ ?_
        · exact mul_le_mul hcw (norm_fderiv_pow_le p hw) (norm_nonneg _)
            (by linarith [Nat.cast_nonneg (α := ℝ) p])
        · exact mul_le_mul hwp hcomp (norm_nonneg _) zero_le_one
    _ = ((p : ℝ) + kap k) * p + Cg := by rw [one_mul]

/-- Conjugation preserves the fderiv norm bound. -/
lemma norm_fderiv_conjF_le {g : ℂ → ℂ} {w : ℂ} (hg : DifferentiableAt ℝ g w) :
    ‖fderiv ℝ (conjF g) w‖ ≤ ‖fderiv ℝ g w‖ := by
  have h1 := (Complex.conjCLE.toContinuousLinearMap.hasFDerivAt
    (x := g w)).comp w hg.hasFDerivAt
  have hFD : HasFDerivAt (conjF g)
      (Complex.conjCLE.toContinuousLinearMap.comp (fderiv ℝ g w)) w := by
    refine h1.congr_of_eventuallyEq (Filter.Eventually.of_forall (fun z => ?_))
    simp [conjF, Function.comp]
  rw [hFD.fderiv]
  refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) (fun v => ?_)
  rw [ContinuousLinearMap.comp_apply]
  calc ‖Complex.conjCLE.toContinuousLinearMap (fderiv ℝ g w v)‖
      = ‖fderiv ℝ g w v‖ := by
        simp [Complex.conjCLE]
    _ ≤ ‖fderiv ℝ g w‖ * ‖v‖ := (fderiv ℝ g w).le_opNorm v

/-! ### The per-mode bounds for `fam` -/

lemma differentiableAt_modeS (k p : ℕ) (w : ℂ) : DifferentiableAt ℝ (modeS k p) w :=
  ((contDiff_modeS k p).differentiable (by simp)).differentiableAt

/-- `‖fam(n)(w)‖ ≤ (|ℓ(n)| + κ)` on the closed disk. -/
lemma norm_fam_le (hk2 : 2 ≤ k) (n : ℤ) {w : ℂ} (hw : ‖w‖ ≤ 1) :
    ‖fam k r n w‖ ≤ (((lz k r n).natAbs : ℝ) + kap k) := by
  have hκ0 : 0 ≤ kap k := (kap_pos hk2).le
  have hbase : ∀ p : ℕ, ‖modeS k p w‖ ≤ ((p : ℝ) + kap k) := by
    intro p
    rw [modeS, norm_mul, Complex.norm_real, Real.norm_eq_abs]
    have h1 : |(p : ℝ) + groundR k w| ≤ (p : ℝ) + kap k := by
      calc |(p : ℝ) + groundR k w| ≤ |(p : ℝ)| + |groundR k w| := abs_add_le _ _
        _ ≤ (p : ℝ) + kap k := by
            rw [abs_of_nonneg (Nat.cast_nonneg p)]
            linarith [abs_groundR_le hk2 w]
    have h2 : ‖w ^ p‖ ≤ 1 := by
      rw [norm_pow]; exact pow_le_one₀ (norm_nonneg w) hw
    calc |(p : ℝ) + groundR k w| * ‖w ^ p‖ ≤ ((p : ℝ) + kap k) * 1 :=
          mul_le_mul h1 h2 (norm_nonneg _) (by linarith [Nat.cast_nonneg (α := ℝ) p])
      _ = (p : ℝ) + kap k := mul_one _
  unfold fam
  split
  · exact hbase _
  · show ‖conjF (modeS k (lz k r n).natAbs) w‖ ≤ _
    simp only [conjF, RCLike.norm_conj]
    exact hbase _

/-- `‖∇fam(n)(w)‖ ≤ (|ℓ(n)| + κ)·|ℓ(n)| + C_g` on the closed disk. -/
lemma norm_fderiv_fam_le (hk2 : 2 ≤ k) (n : ℤ) {Cg : ℝ}
    (hCg : ∀ w : ℂ, ‖w‖ ≤ 1 → ‖fderiv ℝ (groundR k) w‖ ≤ Cg)
    {w : ℂ} (hw : ‖w‖ ≤ 1) :
    ‖fderiv ℝ (fam k r n) w‖
      ≤ (((lz k r n).natAbs : ℝ) + kap k) * ((lz k r n).natAbs : ℝ) + Cg := by
  unfold fam
  split
  · exact_mod_cast norm_fderiv_modeS_le hk2 _ hCg hw
  · refine le_trans (norm_fderiv_conjF_le (differentiableAt_modeS k _ w)) ?_
    exact_mod_cast norm_fderiv_modeS_le hk2 _ hCg hw

/-! ### The generic slot ↔ Icc reindex and the weighted `ℓ¹`-mass -/

/-- The `Fin (2N+1)`-sum over `slot` is the `Icc (−N) N`-sum. -/
lemma sum_slot_eq_Icc {α : Type*} [AddCommMonoid α] (N : ℕ) (h : ℤ → α) :
    ∑ i : Fin (2 * N + 1), h (slot N i) = ∑ n ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), h n := by
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

/-- Summability of the `(|ℓ(n)| + c₀)`-weighted coefficient mass, via `|ℓ(n)| ≤ k(|n|+1)`. -/
lemma summable_weight (hk : 3 ≤ k) {η : ℝ} (hη0 : 0 < η) (c₀ : ℝ) (hc₀ : 0 ≤ c₀) :
    Summable (fun n : ℤ =>
      ((((lz k r n).natAbs : ℝ) + c₀) * ‖Parseval.fc (psiF η) n‖)) := by
  have h1 := (KsIndex.ArcSmooth.summable_abs_mul_fc_psiF η hη0).mul_left (k : ℝ)
  have h2 := (KsIndex.ArcSmooth.summable_fc_psiF η hη0).mul_left ((k : ℝ) + c₀)
  refine Summable.of_nonneg_of_le
    (fun n => mul_nonneg (add_nonneg (Nat.cast_nonneg _) hc₀) (norm_nonneg _))
    (fun n => ?_) (h1.add h2)
  have hlz : ((lz k r n).natAbs : ℝ) ≤ (k : ℝ) * |(n : ℝ)| + (k : ℝ) := by
    have hZ : (lz k r n).natAbs ≤ k * n.natAbs + k := by
      unfold lz
      have h := Int.natAbs_add_le ((k : ℤ) * n) ((k - r : ℕ) : ℤ)
      have h2 : ((k : ℤ) * n).natAbs = k * n.natAbs := by
        rw [Int.natAbs_mul, Int.natAbs_natCast]
      have h3 : (((k - r : ℕ) : ℤ)).natAbs ≤ k := by
        rw [Int.natAbs_natCast]
        omega
      omega
    calc ((lz k r n).natAbs : ℝ) ≤ ((k * n.natAbs + k : ℕ) : ℝ) := by exact_mod_cast hZ
      _ = (k : ℝ) * |(n : ℝ)| + (k : ℝ) := by
          push_cast [Nat.cast_natAbs]
          ring
  calc (((lz k r n).natAbs : ℝ) + c₀) * ‖Parseval.fc (psiF η) n‖
      ≤ ((k : ℝ) * |(n : ℝ)| + ((k : ℝ) + c₀)) * ‖Parseval.fc (psiF η) n‖ := by
        refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
        linarith
    _ = (k : ℝ) * (|(n : ℝ)| * ‖Parseval.fc (psiF η) n‖)
        + ((k : ℝ) + c₀) * ‖Parseval.fc (psiF η) n‖ := by ring

/-! ### The N-uniform disk bounds -/

/-- **Uniform disk bounds for the witness**: there are `Mη, Dη` (independent of `N`)
bounding the value and the real Fréchet derivative operator norm of
`Psi k r N (fc (psiF η))` on the closed disk. -/
theorem Psi_disk_bounds (hk : 3 ≤ k) (hr1 : 1 ≤ r) (hrk : r ≤ k - 1)
    {η : ℝ} (hη0 : 0 < η) :
    ∃ Mη Dη : ℝ, 0 ≤ Mη ∧ 0 ≤ Dη ∧
      (∀ N : ℕ, ∀ w : ℂ, ‖w‖ ≤ 1 →
        ‖Psi k r N (Parseval.fc (psiF η)) w‖ ≤ Mη) ∧
      (∀ N : ℕ, ∀ w : ℂ, ‖w‖ ≤ 1 →
        ‖fderiv ℝ (Psi k r N (Parseval.fc (psiF η))) w‖ ≤ Dη) := by
  have hk2 : 2 ≤ k := by omega
  obtain ⟨Cg, hCg0, hCg⟩ := exists_groundR_fderiv_bound k
  have hκ0 : 0 ≤ kap k := (kap_pos hk2).le
  set t := Parseval.fc (psiF η) with ht
  -- the two weighted masses
  have hsumM := summable_weight (r := r) hk hη0 (kap k) hκ0
  have hsumD := summable_weight (r := r) hk hη0 (kap k + Cg) (by positivity)
  have hnnM : ∀ n : ℤ, 0 ≤ (((lz k r n).natAbs : ℝ) + kap k) * ‖t n‖ := fun n =>
    mul_nonneg (add_nonneg (Nat.cast_nonneg _) hκ0) (norm_nonneg _)
  have hnnD : ∀ n : ℤ, 0 ≤ (((lz k r n).natAbs : ℝ) + (kap k + Cg)) * ‖t n‖ := fun n =>
    mul_nonneg (add_nonneg (Nat.cast_nonneg _) (add_nonneg hκ0 hCg0)) (norm_nonneg _)
  refine ⟨∑' n : ℤ, ((((lz k r n).natAbs : ℝ) + kap k) * ‖t n‖),
    ∑' n : ℤ, ((((lz k r n).natAbs : ℝ) + (kap k + Cg)) * ‖t n‖),
    tsum_nonneg hnnM, tsum_nonneg hnnD,
    fun N w hw => ?_, fun N w hw => ?_⟩
  -- the value bound
  · unfold Psi
    refine le_trans (norm_sum_le _ _) ?_
    have hterm : ∀ i : Fin (2 * N + 1),
        ‖coefOf k r t (slot N i) • fam k r (slot N i) w‖
          ≤ (((lz k r (slot N i)).natAbs : ℝ) + kap k) * ‖t (slot N i)‖ := by
      intro i
      rw [norm_smul]
      have hcoef : ‖coefOf k r t (slot N i)‖ ≤ ‖t (slot N i)‖ :=
        KsIndex.ModeCorr.norm_coefOf_le hk hr1 hrk t _
      calc ‖coefOf k r t (slot N i)‖ * ‖fam k r (slot N i) w‖
          ≤ ‖t (slot N i)‖ * ((((lz k r (slot N i)).natAbs : ℝ) + kap k)) :=
            mul_le_mul hcoef (norm_fam_le hk2 _ hw) (norm_nonneg _) (norm_nonneg _)
        _ = (((lz k r (slot N i)).natAbs : ℝ) + kap k) * ‖t (slot N i)‖ := mul_comm _ _
    refine le_trans (Finset.sum_le_sum (fun i _ => hterm i)) ?_
    rw [sum_slot_eq_Icc N (fun n => (((lz k r n).natAbs : ℝ) + kap k) * ‖t n‖)]
    exact Summable.sum_le_tsum _ (fun n _ => hnnM n) hsumM
  -- the gradient bound
  · have hsumFD' : HasFDerivAt (∑ i : Fin (2 * N + 1),
        coefOf k r t (slot N i) • fam k r (slot N i))
        (∑ i : Fin (2 * N + 1),
          coefOf k r t (slot N i) • fderiv ℝ (fam k r (slot N i)) w) w :=
      HasFDerivAt.sum (fun i _ =>
        ((((contDiff_fam k r (slot N i)).differentiable
          (by simp)).differentiableAt).hasFDerivAt).const_smul (coefOf k r t (slot N i)))
    have hsumFD : HasFDerivAt (fun w : ℂ => ∑ i : Fin (2 * N + 1),
        coefOf k r t (slot N i) • fam k r (slot N i) w)
        (∑ i : Fin (2 * N + 1),
          coefOf k r t (slot N i) • fderiv ℝ (fam k r (slot N i)) w) w := by
      refine hsumFD'.congr_of_eventuallyEq (Filter.Eventually.of_forall (fun z => ?_))
      simp [Finset.sum_apply]
    have hfder : fderiv ℝ (Psi k r N t) w
        = ∑ i : Fin (2 * N + 1),
            coefOf k r t (slot N i) • fderiv ℝ (fam k r (slot N i)) w := hsumFD.fderiv
    rw [hfder]
    refine le_trans (norm_sum_le _ _) ?_
    have hterm : ∀ i : Fin (2 * N + 1),
        ‖coefOf k r t (slot N i) • fderiv ℝ (fam k r (slot N i)) w‖
          ≤ (((lz k r (slot N i)).natAbs : ℝ) + (kap k + Cg)) * ‖t (slot N i)‖ := by
      intro i
      rw [norm_smul]
      set p : ℕ := (lz k r (slot N i)).natAbs with hp
      have hp1 : 1 ≤ p := one_le_natAbs_lz hk hr1 hrk _
      have hcoef : ‖coefOf k r t (slot N i)‖ * ((p : ℝ)) ≤ ‖t (slot N i)‖ := by
        rw [coefOf, norm_div, Complex.norm_natCast, ← hp]
        rw [div_mul_eq_mul_div, mul_div_assoc, div_self (by exact_mod_cast (by omega : p ≠ 0)),
          mul_one]
      have hfam := norm_fderiv_fam_le (r := r) hk2 (slot N i) hCg hw
      rw [← hp] at hfam
      calc ‖coefOf k r t (slot N i)‖ * ‖fderiv ℝ (fam k r (slot N i)) w‖
          ≤ ‖coefOf k r t (slot N i)‖ * (((p : ℝ) + kap k) * (p : ℝ) + Cg) :=
            mul_le_mul_of_nonneg_left hfam (norm_nonneg _)
        _ = ‖coefOf k r t (slot N i)‖ * (p : ℝ) * ((p : ℝ) + kap k)
            + ‖coefOf k r t (slot N i)‖ * Cg := by ring
        _ ≤ ‖t (slot N i)‖ * ((p : ℝ) + kap k) + ‖t (slot N i)‖ * Cg := by
            refine add_le_add ?_ ?_
            · exact mul_le_mul_of_nonneg_right hcoef (by positivity)
            · exact mul_le_mul_of_nonneg_right
                (KsIndex.ModeCorr.norm_coefOf_le hk hr1 hrk t _) hCg0
        _ = ((p : ℝ) + (kap k + Cg)) * ‖t (slot N i)‖ := by ring
    refine le_trans (Finset.sum_le_sum (fun i _ => hterm i)) ?_
    rw [sum_slot_eq_Icc N (fun n => (((lz k r n).natAbs : ℝ) + (kap k + Cg)) * ‖t n‖)]
    exact Summable.sum_le_tsum _ (fun n _ => hnnD n) hsumD

end KsIndex.ModeGrad
