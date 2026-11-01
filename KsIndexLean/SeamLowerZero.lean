module

/-
# A negative direction in the trivial rotation class

For `k ≥ 3`, this file proves
`1 ≤ formIndex (Qd k) (NatCc k true true ⊓ Erot1 k 0)`.
The witness `truncConst k ε` is the puncture cutoff `cutPC k ε` on the
closed disk and zero outside. It belongs to the natural pure-Neumann
domain and is invariant under the specified rotation.

Its disk energy is the cutoff Dirichlet energy minus its potential energy.
The former tends to zero as `ε → 0+`, by the logarithmic cutoff bound.
For `ε ≤ 1/2`, the cutoff equals one on the closed disk of radius `1/2`,
where the integral of the potential is strictly positive. A sufficiently
small positive `ε` therefore gives negative energy, and the complex span
of this witness gives the stated index lower bound.

This proves the extra direction needed in the trivial rotation class;
the matching upper bound and exact pure-Neumann count are separate results.
-/
public import KsIndexLean.SeamLowerCount

@[expose] public section


noncomputable section

open Complex MeasureTheory Filter Topology
open scoped ContDiff

namespace KsIndex.SingleDisk

open KsIndex.Surface KsIndex.SurfaceForm KsIndex.SurfaceSym KsIndex.FormIndex KsIndex.Bracket
  KsIndex.SingleDiskBridge KsIndex.PunctureCutoff KsIndex.CutoffContinuity

variable {k : ℕ}

/-! ### The cut-off constant mode -/

/-- The class-`0` constant test mode, truncated to the closed disk. -/
def truncConst (k : ℕ) (ε : ℝ) (w : ℂ) : ℂ := if ‖w‖ ≤ 1 then cutPC k ε w else 0

lemma truncConst_eq_of_mem {ε : ℝ} {w : ℂ} (hw : w ∈ disk) :
    truncConst k ε w = cutPC k ε w := by
  have h1 : ‖w‖ < 1 := by simpa [disk] using hw
  simp [truncConst, h1.le]

/-- `cutPC` is globally smooth. -/
lemma contDiff_cutPC (hk : 1 ≤ k) {ε : ℝ} (h0 : 0 < ε) (h1 : ε < 1) :
    ContDiff ℝ ∞ (cutPC k ε) :=
  Complex.ofRealCLM.contDiff.comp (cutP_contDiff k h0 h1)

/-- **The class-`0` constant mode is a natural pure-Neumann test function.** -/
theorem truncConst_mem_NatCc (hk : 1 ≤ k) {ε : ℝ} (h0 : 0 < ε) (h1 : ε < 1) :
    truncConst k ε ∈ NatCc k true true := by
  have hF := contDiff_cutPC hk h0 h1
  have hone : ∀ w₀, OneSided (truncConst k ε) w₀ := fun w₀ =>
    ⟨cutPC k ε, hF.contDiffAt, Eventually.of_forall fun w hw => truncConst_eq_of_mem hw⟩
  rw [mem_NatCc]
  refine ⟨hF.contDiffOn.congr fun w hw => truncConst_eq_of_mem hw,
    fun w _ => hone w, fun w _ => hone w, fun w hw => ?_,
    ⟨ε ^ 2, by positivity, fun w ⟨p, hp, hwp⟩ => ?_⟩⟩
  · simp [truncConst, not_le.mpr hw]
  · unfold truncConst
    split_ifs
    · simp [cutPC, cutP_eq_zero hk h0 h1 ⟨p, hp, hwp.le⟩]
    · rfl

/-- The constant mode is rotation-invariant. -/
lemma truncConst_rot (hk : 1 ≤ k) (ε : ℝ) :
    rot1 (rotUnit k : ℂ) (truncConst k ε) = truncConst k ε := by
  funext w
  have ha : ‖(rotUnit k : ℂ)‖ = 1 := Circle.norm_coe _
  have hak : (rotUnit k : ℂ) ^ (2 * k) = 1 := by
    rw [pow_mul', rotUnit_pow (by omega), one_pow]
  simp only [rot1_apply, truncConst, norm_mul, ha, one_mul]
  split_ifs with h
  · simp only [cutPC, cutP_rot hk ε ha hak]
  · rfl

/-- The constant mode lies in the trivial rotation class. -/
theorem truncConst_mem_Erot1 (hk : 1 ≤ k) (ε : ℝ) : truncConst k ε ∈ Erot1 k 0 := by
  rw [Erot1, Module.End.mem_eigenspace_iff, truncConst_rot hk ε]
  simp

/-! ### `Qd` of the cut-off constant -/

/-- `Qd` of the truncated constant is the cut-off's disk energy. -/
lemma Qd_truncConst_eq (hk : 2 ≤ k) {ε : ℝ} :
    Qd k (truncConst k ε)
      = (∫ w in disk, gradSq (cutPC k ε) w) - ∫ w in disk, potV k w * ‖cutPC k ε w‖ ^ 2 := by
  rw [Qd_congr_disk (fun w hw => truncConst_eq_of_mem hw),
    show Qd k (cutPC k ε) = dirichletG k (cutPC k ε) - potentialG k (cutPC k ε) from rfl,
    dirichletG_sub_potentialG hk]

/-! ### The fixed potential floor -/

/-- The potential is positive at a fixed interior point. -/
lemma potV_pos_quarter (hk : 3 ≤ k) : 0 < potV k ((1 / 4 : ℝ) : ℂ) := by
  have hk1 : (0 : ℝ) < (k : ℝ) - 1 := by
    have : (3 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
    linarith
  have hn : ‖((1 / 4 : ℝ) : ℂ)‖ = 1 / 4 := by rw [Complex.norm_real, Real.norm_eq_abs]; norm_num
  rw [potV, hn]
  apply div_pos
  · exact mul_pos (mul_pos (by norm_num) (pow_pos hk1 2)) (pow_pos (by norm_num) _)
  · exact pow_pos (by positivity) 2

/-- **The potential floor**: `∫_{closedBall 0 ½} V > 0`. -/
lemma potFloor_pos (hk : 3 ≤ k) : 0 < ∫ w in Metric.closedBall (0 : ℂ) (1 / 2), potV k w := by
  set w₀ : ℂ := ((1 / 4 : ℝ) : ℂ) with hw₀
  have hcont : Continuous (potV k) := KsIndex.SurfaceForm.continuous_potV k
  have hpos₀ : 0 < potV k w₀ := potV_pos_quarter hk
  have hn₀ : ‖w₀‖ = 1 / 4 := by rw [hw₀, Complex.norm_real, Real.norm_eq_abs]; norm_num
  set U : Set ℂ := Metric.ball (0 : ℂ) (1 / 2) ∩ {w | potV k w₀ / 2 < potV k w} with hU
  have hUopen : IsOpen U := Metric.isOpen_ball.inter (isOpen_lt continuous_const hcont)
  have hw₀U : w₀ ∈ U := by
    refine ⟨?_, ?_⟩
    · rw [Metric.mem_ball, dist_zero_right, hn₀]; norm_num
    · simp only [Set.mem_setOf_eq]; linarith
  have hUsub : U ⊆ Metric.closedBall (0 : ℂ) (1 / 2) := fun w hw =>
    Metric.ball_subset_closedBall hw.1
  have hUvol : 0 < volume U := hUopen.measure_pos volume ⟨w₀, hw₀U⟩
  have hUvolne : volume U ≠ ⊤ :=
    ((measure_mono hUsub).trans_lt (isCompact_closedBall (0 : ℂ) (1 / 2)).measure_lt_top).ne
  have hint : IntegrableOn (potV k) (Metric.closedBall (0 : ℂ) (1 / 2)) :=
    hcont.continuousOn.integrableOn_compact (isCompact_closedBall _ _)
  have hintU : IntegrableOn (potV k) U := hint.mono_set hUsub
  have hnn : ∀ w, 0 ≤ potV k w := KsIndex.SurfaceForm.potV_nonneg k
  -- ∫_{cB} ≥ ∫_U ≥ (potV w₀/2)·vol U > 0
  have hstep1 : ∫ w in U, potV k w ≤ ∫ w in Metric.closedBall (0 : ℂ) (1 / 2), potV k w :=
    setIntegral_mono_set hint (Eventually.of_forall hnn) (HasSubset.Subset.eventuallyLE hUsub)
  haveI hfin : IsFiniteMeasure (volume.restrict U) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact lt_top_iff_ne_top.mpr hUvolne⟩
  have hconstint : IntegrableOn (fun _ : ℂ => potV k w₀ / 2) U := integrable_const _
  have hstep2 : (∫ w in U, potV k w₀ / 2) ≤ ∫ w in U, potV k w :=
    setIntegral_mono_on hconstint hintU hUopen.measurableSet (fun w hw => le_of_lt hw.2)
  have hUint_pos : 0 < ∫ w in U, potV k w₀ / 2 := by
    rw [setIntegral_const, smul_eq_mul]
    exact mul_pos (ENNReal.toReal_pos hUvol.ne' hUvolne) (by linarith)
  linarith [hstep1, hstep2, hUint_pos]

/-! ### `Qd(truncConst) < 0` for small `ε` -/

/-- The cut-off equals `1` on the closed disk of radius `1/2` once `ε ≤ 1/2`. -/
lemma cutP_eq_one_half (hk : 1 ≤ k) {ε : ℝ} (h0 : 0 < ε) (h1 : ε < 1) (hε : ε ≤ 1 / 2)
    {w : ℂ} (hw : w ∈ Metric.closedBall (0 : ℂ) (1 / 2)) : cutP k ε w = 1 := by
  refine cutP_eq_one hk h0 h1 (fun p hp => ?_)
  have hwn : ‖w‖ ≤ 1 / 2 := by rwa [Metric.mem_closedBall, dist_zero_right] at hw
  have hpn : ‖p‖ = 1 := (punctures_subset_slit hk hp).1
  calc ε ≤ 1 / 2 := hε
    _ ≤ ‖p‖ - ‖w‖ := by rw [hpn]; linarith
    _ ≤ ‖w - p‖ := by rw [norm_sub_rev]; exact norm_sub_norm_le p w

/-- The potential term of the cut-off stays above the fixed floor when `ε ≤ ½`. -/
lemma potInt_ge_floor (hk : 3 ≤ k) {ε : ℝ} (h0 : 0 < ε) (h1 : ε < 1) (hε : ε ≤ 1 / 2) :
    (∫ w in Metric.closedBall (0 : ℂ) (1 / 2), potV k w)
      ≤ ∫ w in disk, potV k w * ‖cutPC k ε w‖ ^ 2 := by
  have hk1 : 1 ≤ k := by omega
  have hcont : Continuous (fun w => potV k w * ‖cutPC k ε w‖ ^ 2) :=
    (KsIndex.SurfaceForm.continuous_potV k).mul (((contDiff_cutPC hk1 h0 h1).continuous).norm.pow 2)
  have hintcb : IntegrableOn (fun w => potV k w * ‖cutPC k ε w‖ ^ 2)
      (Metric.closedBall (0 : ℂ) 1) :=
    hcont.continuousOn.integrableOn_compact (isCompact_closedBall _ _)
  have hintd : IntegrableOn (fun w => potV k w * ‖cutPC k ε w‖ ^ 2) disk :=
    hintcb.mono_set (by
      rw [show disk = Metric.ball (0 : ℂ) 1 from rfl]; exact Metric.ball_subset_closedBall)
  have hnn : ∀ w, 0 ≤ potV k w * ‖cutPC k ε w‖ ^ 2 :=
    fun w => mul_nonneg (KsIndex.SurfaceForm.potV_nonneg k w) (sq_nonneg _)
  have hsub : Metric.closedBall (0 : ℂ) (1 / 2) ⊆ disk := by
    rw [show disk = Metric.ball (0 : ℂ) 1 from rfl]
    exact (Metric.closedBall_subset_ball (by norm_num))
  have hcongr : ∫ w in Metric.closedBall (0 : ℂ) (1 / 2), potV k w * ‖cutPC k ε w‖ ^ 2
      = ∫ w in Metric.closedBall (0 : ℂ) (1 / 2), potV k w := by
    refine setIntegral_congr_fun measurableSet_closedBall (fun w hw => ?_)
    rw [cutPC, cutP_eq_one_half hk1 h0 h1 hε hw]
    simp
  rw [← hcongr]
  exact setIntegral_mono_set hintd (Eventually.of_forall hnn)
    (HasSubset.Subset.eventuallyLE hsub)

/-- **The cut-off constant has negative energy for small `ε`.** -/
theorem exists_eps_truncConst_neg (hk : 3 ≤ k) :
    ∃ ε : ℝ, 0 < ε ∧ ε < 1 ∧ Qd k (truncConst k ε) < 0 := by
  have hk2 : 2 ≤ k := by omega
  have hk1 : 1 ≤ k := by omega
  set c : ℝ := ∫ w in Metric.closedBall (0 : ℂ) (1 / 2), potV k w with hc
  have hcpos : 0 < c := potFloor_pos hk
  set M : ℝ := 4 * Real.pi * (pF k).card ^ 2 * Mψ ^ 2 with hM
  have hinv : Tendsto (fun ε : ℝ => (Lε ε)⁻¹) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    apply Filter.Tendsto.inv_tendsto_atTop
    have hL : Tendsto (fun ε : ℝ => Lε ε) (𝓝[>] (0 : ℝ)) Filter.atTop := by
      simp only [Lε]
      first
        | exact tendsto_neg_atTop_iff.mpr Real.tendsto_log_nhdsGT_zero
        | exact Filter.tendsto_neg_atTop_iff.mpr Real.tendsto_log_nhdsGT_zero
        | exact Real.tendsto_log_nhdsGT_zero.neg_atBot
    exact hL
  have htend : Tendsto (fun ε : ℝ => M * (Lε ε)⁻¹) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    simpa using hinv.const_mul M
  have hev1 : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ε < 1 :=
    (Filter.eventually_of_mem (Iio_mem_nhds (show (0 : ℝ) < 1 by norm_num)) fun x hx => hx).filter_mono
      nhdsWithin_le_nhds
  have hev0 : ∀ᶠ ε in 𝓝[>] (0 : ℝ), (0 : ℝ) < ε := eventually_mem_nhdsWithin.mono fun _ h => h
  have hev2 : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ε ≤ 1 / 2 :=
    (Filter.eventually_of_mem (Iic_mem_nhds (show (0 : ℝ) < 1 / 2 by norm_num)) fun x hx => hx).filter_mono
      nhdsWithin_le_nhds
  have hev4 : ∀ᶠ ε in 𝓝[>] (0 : ℝ), M * (Lε ε)⁻¹ < c :=
    (htend.eventually (Iio_mem_nhds hcpos)).mono fun ε h => h
  obtain ⟨ε, hε0, hε1, hεhalf, hεc⟩ := (hev0.and (hev1.and (hev2.and hev4))).exists
  refine ⟨ε, hε0, hε1, ?_⟩
  rw [Qd_truncConst_eq hk2]
  have hup : (∫ w in disk, gradSq (cutPC k ε) w) ≤ M * (Lε ε)⁻¹ := by
    rw [hM, ← div_eq_mul_inv]; exact energy_cutP_le k hε0 hε1
  have hlow : c ≤ ∫ w in disk, potV k w * ‖cutPC k ε w‖ ^ 2 := potInt_ge_floor hk hε0 hε1 hεhalf
  linarith

/-! ### The class-`0` lower bound -/

/-- **The pure-Neumann seam lower bound in class `0`** for `k ≥ 3`, supplied
by the rotation-invariant cutoff of the constant function. -/
theorem one_le_seamNat_zero (hk : 3 ≤ k) :
    (1 : ℕ∞) ≤ formIndex (Qd k) (NatCc k true true ⊓ Erot1 k 0) := by
  have hk1 : 1 ≤ k := by omega
  have hk2 : 2 ≤ k := by omega
  obtain ⟨ε, hε0, hε1, hneg⟩ := exists_eps_truncConst_neg hk
  have hsm : ContDiffOn ℝ ∞ (truncConst k ε) disk :=
    (contDiff_cutPC hk1 hε0 hε1).contDiffOn.congr fun w hw => truncConst_eq_of_mem hw
  have key : ((1 : ℕ) : ℕ∞) ≤ formIndex (Qd k) (NatCc k true true ⊓ Erot1 k 0) := by
    refine formIndex_ge_of_neg (Qd_zero k) ![truncConst k ε] (fun i => ?_) (fun c hc => ?_)
    · fin_cases i
      exact Submodule.mem_inf.mpr ⟨truncConst_mem_NatCc hk1 hε0 hε1, truncConst_mem_Erot1 hk1 ε⟩
    · have hc0 : c 0 ≠ 0 := fun h => hc (funext fun i => by fin_cases i; exact h)
      simp only [Fin.sum_univ_one, Matrix.cons_val_zero]
      rw [Qd_smul hk2 hsm]
      exact mul_neg_of_pos_of_neg (pow_pos (norm_pos_iff.mpr hc0) 2) hneg
  simpa using key

end KsIndex.SingleDisk
