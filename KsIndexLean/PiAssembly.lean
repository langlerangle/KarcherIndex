module

/-
# The (Π) mode-sum identity for the disk Jacobi form

For a globally `C¹` `G : ℂ → ℂ`,
  `Qd k G = 2π · ∑_ℓ ∫₀¹ lhsC k |ℓ| (Fm G ℓ) (FmD G ℓ)`   (`Qd_eq_tsum`, `2 ≤ k`),
the disk Jacobi form written as a sum over angular modes of the exactly-solvable radial forms.
The proof combines polar change of variables (`BallPolar`), per-circle mode sums
(`PolarAssembly`), and the nonnegative sum/integral interchange (`NonnegSwap`,
with a proof contributed by Aristotle). Separate summability of the Dirichlet and
potential contributions permits subtraction via `tsum_sub`.
-/
public import KsIndexLean.BallPolar
public import KsIndexLean.PolarAssembly
public import KsIndexLean.NonnegSwap

@[expose] public section


noncomputable section

open Complex Real MeasureTheory intervalIntegral Set
open KsIndex.Parseval KsIndex.FourierMode KsIndex.PolarGrad KsIndex.PolarAssembly KsIndex.Surface
  KsIndex.Radial KsIndex.SingleDiskBridge KsIndex.BallPolar

namespace KsIndex.PiAssembly

variable {k : ℕ}

/-- The flat gradient density of a `C¹` function is continuous. -/
lemma continuous_gradSq {G : ℂ → ℂ} (hG : ContDiff ℝ 1 G) : Continuous (gradSq G) := by
  have hfd : Continuous (fderiv ℝ G) := hG.continuous_fderiv one_ne_zero
  have h1 : Continuous fun w : ℂ => ‖fderiv ℝ G w 1‖ ^ 2 :=
    ((hfd.clm_apply continuous_const).norm.pow 2)
  have h2 : Continuous fun w : ℂ => ‖fderiv ℝ G w I‖ ^ 2 :=
    ((hfd.clm_apply continuous_const).norm.pow 2)
  have h : Continuous fun w : ℂ => ‖fderiv ℝ G w 1‖ ^ 2 + ‖fderiv ℝ G w I‖ ^ 2 := h1.add h2
  exact h

/-- Points of the circle of radius `r ≤ 1` lie in the closed unit disk. -/
lemma mem_closedBall_of_le {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1) (θ : ℝ) :
    (r : ℂ) * Complex.exp ((θ : ℂ) * I) ∈ Metric.closedBall (0 : ℂ) 1 := by
  rw [Metric.mem_closedBall, dist_zero_right, norm_mul, norm_exp_I_mul, mul_one,
    Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr0]
  exact hr1

/-- `w ↦ V·‖G‖²`, the potential density, is continuous for continuous `G`. -/
lemma continuous_potVsq {G : ℂ → ℂ} (hG : Continuous G) :
    Continuous fun w : ℂ => potV k w * ‖G w‖ ^ 2 := by
  have hpv : Continuous fun w : ℂ => potV k w := by
    have : (fun w : ℂ => potV k w) = fun w : ℂ => Vrad k ‖w‖ := funext (potV_eq_Vrad k)
    rw [this]; exact (continuous_Vrad k).comp continuous_norm
  exact hpv.mul (hG.norm.pow 2)

/-- A circle-integral bound: if a nonnegative continuous `f` is `≤ M` on the closed disk, then
`∫₀^{2π} r·f(r e^{iθ}) dθ ≤ 2π·M` for `r ∈ (0,1]`. -/
lemma density_bound {f : ℂ → ℝ} (hfc : Continuous f) (hfnn : ∀ w, 0 ≤ f w) {M : ℝ}
    (hM : ∀ w ∈ Metric.closedBall (0 : ℂ) 1, f w ≤ M) {r : ℝ} (hr : r ∈ Ioc (0 : ℝ) 1) :
    (∫ θ in (0 : ℝ)..2 * π, r * f ((r : ℂ) * Complex.exp ((θ : ℂ) * I))) ≤ 2 * π * M := by
  have hcont : Continuous fun θ : ℝ => r * f ((r : ℂ) * Complex.exp ((θ : ℂ) * I)) :=
    continuous_const.mul (hfc.comp (by fun_prop))
  have hpt : ∀ θ ∈ Icc (0 : ℝ) (2 * π), r * f ((r : ℂ) * Complex.exp ((θ : ℂ) * I)) ≤ M := by
    intro θ _
    calc r * f ((r : ℂ) * Complex.exp ((θ : ℂ) * I))
        ≤ 1 * f ((r : ℂ) * Complex.exp ((θ : ℂ) * I)) :=
          mul_le_mul_of_nonneg_right hr.2 (hfnn _)
      _ = f ((r : ℂ) * Complex.exp ((θ : ℂ) * I)) := one_mul _
      _ ≤ M := hM _ (mem_closedBall_of_le hr.1.le hr.2 θ)
  calc (∫ θ in (0 : ℝ)..2 * π, r * f ((r : ℂ) * Complex.exp ((θ : ℂ) * I)))
      ≤ ∫ _ in (0 : ℝ)..2 * π, M :=
        intervalIntegral.integral_mono_on (by positivity) (hcont.intervalIntegrable _ _)
          intervalIntegrable_const hpt
    _ = 2 * π * M := by rw [intervalIntegral.integral_const, smul_eq_mul, sub_zero]

lemma dirTerm_measurable {G : ℂ → ℂ} (hG : ContDiff ℝ 1 G) (ℓ : ℤ) :
    Measurable (dirTerm G ℓ) := by
  have hFm : Measurable (Fm G ℓ) := (Fm_continuous hG.continuous ℓ).measurable
  have hFmD : Measurable (FmD G ℓ) := (FmD_continuous hG ℓ).measurable
  unfold dirTerm
  fun_prop

lemma potTerm_measurable {G : ℂ → ℂ} (hG : Continuous G) (ℓ : ℤ) :
    Measurable (potTerm k G ℓ) := by
  have hFm : Measurable (Fm G ℓ) := (Fm_continuous hG ℓ).measurable
  have hV : Measurable (Vrad k) := (continuous_Vrad k).measurable
  unfold potTerm
  fun_prop

lemma dirTerm_nonneg (G : ℂ → ℂ) (ℓ : ℤ) {r : ℝ} (hr : 0 ≤ r) : 0 ≤ dirTerm G ℓ r := by
  rw [dirTerm]; positivity

lemma potTerm_nonneg (G : ℂ → ℂ) (ℓ : ℤ) {r : ℝ} (hr : 0 ≤ r) : 0 ≤ potTerm k G ℓ r := by
  rw [potTerm, Vrad]; positivity

/-- Finiteness of the total-density lower integral: if the pointwise sum is bounded by `M` on
`(0,1]`, then `∫⁻ ∑ₗ ofReal(g ℓ r) < ∞`.  This is the hypothesis the nonnegative swap consumes. -/
lemma lintegral_tsum_ofReal_ne_top {g : ℤ → ℝ → ℝ} {M : ℝ}
    (hnn : ∀ ℓ, ∀ r ∈ Ioc (0 : ℝ) 1, 0 ≤ g ℓ r)
    (hsum : ∀ r ∈ Ioc (0 : ℝ) 1, Summable fun ℓ => g ℓ r)
    (hbd : ∀ r ∈ Ioc (0 : ℝ) 1, ∑' ℓ, g ℓ r ≤ M) :
    (∫⁻ r in Ioc (0 : ℝ) 1, ∑' ℓ : ℤ, ENNReal.ofReal (g ℓ r)) ≠ ⊤ := by
  have hle : (∫⁻ r in Ioc (0 : ℝ) 1, ∑' ℓ : ℤ, ENNReal.ofReal (g ℓ r))
      ≤ ∫⁻ _ in Ioc (0 : ℝ) 1, ENNReal.ofReal M := by
    refine setLIntegral_mono' measurableSet_Ioc (fun r hr => ?_)
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun ℓ => hnn ℓ r hr) (hsum r hr)]
    exact ENNReal.ofReal_le_ofReal (hbd r hr)
  have hb : (∫⁻ _ in Ioc (0 : ℝ) 1, ENNReal.ofReal M) ≠ ⊤ := by
    rw [setLIntegral_const, Real.volume_Ioc, sub_zero]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top
  exact ne_top_of_le_ne_top hb hle

/-- The per-mode densities combine to the exactly-solvable radial form:
`dirTerm ℓ r − potTerm ℓ r = lhsC k |ℓ| (Fm G ℓ) (FmD G ℓ) r`. -/
lemma dirTerm_sub_potTerm (G : ℂ → ℂ) (ℓ : ℤ) (r : ℝ) :
    dirTerm G ℓ r - potTerm k G ℓ r = lhsC k ℓ.natAbs (Fm G ℓ) (FmD G ℓ) r := by
  have hn : ((ℓ.natAbs : ℕ) : ℝ) ^ 2 = (ℓ : ℝ) ^ 2 := by
    rw [Nat.cast_natAbs, Int.cast_abs, sq_abs]
  rw [dirTerm, potTerm, lhsC, hn]
  ring

/-- **A disk energy as a mode sum.**  If the circle integral of a continuous disk
density `fdisk` is `2π ∑_ℓ g ℓ r` per radius, with `g` a nonnegative measurable family that is
pointwise summable with finite total lower integral, then the disk integral of `fdisk` is
`2π ∑_ℓ ∫₀¹ g ℓ`, the integrals `∫₀¹ g ℓ` are summable, and each `g ℓ` is interval integrable. -/
lemma energy_eq {fdisk : ℂ → ℝ} {g : ℤ → ℝ → ℝ} (hfc : Continuous fdisk)
    (hcirc : ∀ r ∈ Ioc (0 : ℝ) 1,
      (∫ θ in (0 : ℝ)..2 * π, r * fdisk ((r : ℂ) * Complex.exp ((θ : ℂ) * I)))
        = 2 * π * ∑' ℓ, g ℓ r)
    (hmeas : ∀ ℓ, Measurable (g ℓ))
    (hnn : ∀ ℓ, ∀ r ∈ Ioc (0 : ℝ) 1, 0 ≤ g ℓ r)
    (hsum : ∀ r ∈ Ioc (0 : ℝ) 1, Summable fun ℓ => g ℓ r)
    (hfin : (∫⁻ r in Ioc (0 : ℝ) 1, ∑' ℓ : ℤ, ENNReal.ofReal (g ℓ r)) ≠ ⊤) :
    (∫ w in disk, fdisk w) = 2 * π * ∑' ℓ, ∫ r in (0 : ℝ)..1, g ℓ r
      ∧ (Summable fun ℓ => ∫ r in (0 : ℝ)..1, g ℓ r)
      ∧ ∀ ℓ, IntervalIntegrable (g ℓ) volume 0 1 := by
  obtain ⟨hint, hswap, hsummable⟩ :=
    NonnegSwap.integral_Ioc_tsum_of_lintegral_ne_top hmeas hnn hsum hfin
  have hII : ∀ ℓ, IntervalIntegrable (g ℓ) volume 0 1 := fun ℓ =>
    (intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).2 (hint ℓ)
  refine ⟨?_, ?_, hII⟩
  · rw [show (disk : Set ℂ) = Metric.ball (0 : ℂ) 1 from rfl, setIntegral_ball_polar hfc,
      intervalIntegral.integral_of_le zero_le_one,
      setIntegral_congr_fun measurableSet_Ioc (fun r hr => hcirc r hr),
      MeasureTheory.integral_const_mul, hswap]
    exact congrArg _ (tsum_congr fun ℓ => (intervalIntegral.integral_of_le zero_le_one).symm)
  · simpa only [← intervalIntegral.integral_of_le zero_le_one] using hsummable

/-- **The (Π) mode-sum identity.**  For globally `C¹` `G` and `k ≥ 2`, the disk Jacobi form is the
sum over angular modes of the exactly-solvable radial forms:
`Qd k G = 2π ∑_ℓ ∫₀¹ lhsC k |ℓ| (Fm G ℓ) (FmD G ℓ)`. -/
theorem Qd_eq_tsum {G : ℂ → ℂ} (hG : ContDiff ℝ 1 G) (hk : 2 ≤ k) :
    Qd k G = 2 * π * ∑' ℓ : ℤ, ∫ r in (0 : ℝ)..1, lhsC k ℓ.natAbs (Fm G ℓ) (FmD G ℓ) r := by
  have hpi : (2 * π : ℝ) ≠ 0 := by positivity
  have hgnn : ∀ w, 0 ≤ gradSq G w := fun w => by rw [gradSq]; positivity
  have hpnn : ∀ w, 0 ≤ potV k w * ‖G w‖ ^ 2 :=
    fun w => mul_nonneg (by unfold potV; positivity) (sq_nonneg _)
  obtain ⟨MD, hMD⟩ := (isCompact_closedBall (0 : ℂ) 1).exists_bound_of_continuousOn
    (continuous_gradSq hG).continuousOn
  obtain ⟨MP, hMP⟩ := (isCompact_closedBall (0 : ℂ) 1).exists_bound_of_continuousOn
    (continuous_potVsq (k := k) hG.continuous).continuousOn
  have hMDbd : ∀ w ∈ Metric.closedBall (0 : ℂ) 1, gradSq G w ≤ MD := fun w hw =>
    (le_abs_self _).trans (by rw [← Real.norm_eq_abs]; exact hMD w hw)
  have hMPbd : ∀ w ∈ Metric.closedBall (0 : ℂ) 1, potV k w * ‖G w‖ ^ 2 ≤ MP := fun w hw =>
    (le_abs_self _).trans (by rw [← Real.norm_eq_abs]; exact hMP w hw)
  -- Dirichlet energy
  have hcircD : ∀ r ∈ Ioc (0 : ℝ) 1,
      (∫ θ in (0 : ℝ)..2 * π, r * gradSq G ((r : ℂ) * Complex.exp ((θ : ℂ) * I)))
        = 2 * π * ∑' ℓ, dirTerm G ℓ r := fun r hr => by
    rw [(hasSum_dirTerm hG hr.1.ne').tsum_eq, ← mul_assoc, mul_inv_cancel₀ hpi, one_mul]
  have hbdD : ∀ r ∈ Ioc (0 : ℝ) 1, ∑' ℓ, dirTerm G ℓ r ≤ MD := fun r hr => by
    rw [(hasSum_dirTerm hG hr.1.ne').tsum_eq]
    calc (2 * π : ℝ)⁻¹ * (∫ θ in (0 : ℝ)..2 * π, r * gradSq G ((r : ℂ) * Complex.exp ((θ : ℂ) * I)))
        ≤ (2 * π)⁻¹ * (2 * π * MD) :=
          mul_le_mul_of_nonneg_left (density_bound (continuous_gradSq hG) hgnn hMDbd hr)
            (by positivity)
      _ = MD := by rw [← mul_assoc, inv_mul_cancel₀ hpi, one_mul]
  obtain ⟨hDeq, hDsum, hDint⟩ := energy_eq (continuous_gradSq hG) hcircD (dirTerm_measurable hG)
    (fun ℓ r hr => dirTerm_nonneg G ℓ hr.1.le) (fun r hr => (hasSum_dirTerm hG hr.1.ne').summable)
    (lintegral_tsum_ofReal_ne_top (fun ℓ r hr => dirTerm_nonneg G ℓ hr.1.le)
      (fun r hr => (hasSum_dirTerm hG hr.1.ne').summable) hbdD)
  -- Potential energy
  have hcircP : ∀ r ∈ Ioc (0 : ℝ) 1,
      (∫ θ in (0 : ℝ)..2 * π,
        r * (potV k ((r : ℂ) * Complex.exp ((θ : ℂ) * I))
          * ‖G ((r : ℂ) * Complex.exp ((θ : ℂ) * I))‖ ^ 2))
        = 2 * π * ∑' ℓ, potTerm k G ℓ r := fun r hr => by
    rw [(hasSum_potTerm hG.continuous hr.1.le).tsum_eq, ← mul_assoc, mul_inv_cancel₀ hpi, one_mul]
  have hbdP : ∀ r ∈ Ioc (0 : ℝ) 1, ∑' ℓ, potTerm k G ℓ r ≤ MP := fun r hr => by
    rw [(hasSum_potTerm hG.continuous hr.1.le).tsum_eq]
    calc (2 * π : ℝ)⁻¹ * (∫ θ in (0 : ℝ)..2 * π,
            r * (potV k ((r : ℂ) * Complex.exp ((θ : ℂ) * I))
              * ‖G ((r : ℂ) * Complex.exp ((θ : ℂ) * I))‖ ^ 2))
        ≤ (2 * π)⁻¹ * (2 * π * MP) :=
          mul_le_mul_of_nonneg_left (density_bound (continuous_potVsq hG.continuous) hpnn hMPbd hr)
            (by positivity)
      _ = MP := by rw [← mul_assoc, inv_mul_cancel₀ hpi, one_mul]
  obtain ⟨hPeq, hPsum, hPint⟩ := energy_eq (continuous_potVsq hG.continuous) hcircP
    (potTerm_measurable hG.continuous) (fun ℓ r hr => potTerm_nonneg G ℓ hr.1.le)
    (fun r hr => (hasSum_potTerm hG.continuous hr.1.le).summable)
    (lintegral_tsum_ofReal_ne_top (fun ℓ r hr => potTerm_nonneg G ℓ hr.1.le)
      (fun r hr => (hasSum_potTerm hG.continuous hr.1.le).summable) hbdP)
  -- Combine
  rw [show Qd k G = dirichletG k G - potentialG k G from rfl, dirichletG_sub_potentialG hk,
    hDeq, hPeq, ← mul_sub, ← Summable.tsum_sub hDsum hPsum]
  refine congrArg _ (tsum_congr fun ℓ => ?_)
  rw [← intervalIntegral.integral_sub (hDint ℓ) (hPint ℓ)]
  exact intervalIntegral.integral_congr (fun r _ => dirTerm_sub_potTerm G ℓ r)


/-- **The mode integrals are summable.** For globally `C¹` `G` and `k ≥ 2`, the
series displayed in `Qd_eq_tsum` satisfies `Summable`. This is established by
subtracting the separately summable Dirichlet and potential mode integrals. -/
lemma modeTerm_summable {G : ℂ → ℂ} (hG : ContDiff ℝ 1 G) (_hk : 2 ≤ k) :
    Summable (fun ℓ : ℤ => ∫ r in (0 : ℝ)..1, lhsC k ℓ.natAbs (Fm G ℓ) (FmD G ℓ) r) := by
  have hpi : (2 * π : ℝ) ≠ 0 := by positivity
  have hgnn : ∀ w, 0 ≤ gradSq G w := fun w => by rw [gradSq]; positivity
  have hpnn : ∀ w, 0 ≤ potV k w * ‖G w‖ ^ 2 :=
    fun w => mul_nonneg (by unfold potV; positivity) (sq_nonneg _)
  obtain ⟨MD, hMD⟩ := (isCompact_closedBall (0 : ℂ) 1).exists_bound_of_continuousOn
    (continuous_gradSq hG).continuousOn
  obtain ⟨MP, hMP⟩ := (isCompact_closedBall (0 : ℂ) 1).exists_bound_of_continuousOn
    (continuous_potVsq (k := k) hG.continuous).continuousOn
  have hMDbd : ∀ w ∈ Metric.closedBall (0 : ℂ) 1, gradSq G w ≤ MD := fun w hw =>
    (le_abs_self _).trans (by rw [← Real.norm_eq_abs]; exact hMD w hw)
  have hMPbd : ∀ w ∈ Metric.closedBall (0 : ℂ) 1, potV k w * ‖G w‖ ^ 2 ≤ MP := fun w hw =>
    (le_abs_self _).trans (by rw [← Real.norm_eq_abs]; exact hMP w hw)
  have hcircD : ∀ r ∈ Ioc (0 : ℝ) 1,
      (∫ θ in (0 : ℝ)..2 * π, r * gradSq G ((r : ℂ) * Complex.exp ((θ : ℂ) * I)))
        = 2 * π * ∑' ℓ, dirTerm G ℓ r := fun r hr => by
    rw [(hasSum_dirTerm hG hr.1.ne').tsum_eq, ← mul_assoc, mul_inv_cancel₀ hpi, one_mul]
  have hbdD : ∀ r ∈ Ioc (0 : ℝ) 1, ∑' ℓ, dirTerm G ℓ r ≤ MD := fun r hr => by
    rw [(hasSum_dirTerm hG hr.1.ne').tsum_eq]
    calc (2 * π : ℝ)⁻¹
            * (∫ θ in (0 : ℝ)..2 * π, r * gradSq G ((r : ℂ) * Complex.exp ((θ : ℂ) * I)))
        ≤ (2 * π)⁻¹ * (2 * π * MD) :=
          mul_le_mul_of_nonneg_left (density_bound (continuous_gradSq hG) hgnn hMDbd hr)
            (by positivity)
      _ = MD := by rw [← mul_assoc, inv_mul_cancel₀ hpi, one_mul]
  obtain ⟨_, hDsum, hDint⟩ := energy_eq (continuous_gradSq hG) hcircD (dirTerm_measurable hG)
    (fun ℓ r hr => dirTerm_nonneg G ℓ hr.1.le) (fun r hr => (hasSum_dirTerm hG hr.1.ne').summable)
    (lintegral_tsum_ofReal_ne_top (fun ℓ r hr => dirTerm_nonneg G ℓ hr.1.le)
      (fun r hr => (hasSum_dirTerm hG hr.1.ne').summable) hbdD)
  have hcircP : ∀ r ∈ Ioc (0 : ℝ) 1,
      (∫ θ in (0 : ℝ)..2 * π,
        r * (potV k ((r : ℂ) * Complex.exp ((θ : ℂ) * I))
          * ‖G ((r : ℂ) * Complex.exp ((θ : ℂ) * I))‖ ^ 2))
        = 2 * π * ∑' ℓ, potTerm k G ℓ r := fun r hr => by
    rw [(hasSum_potTerm hG.continuous hr.1.le).tsum_eq, ← mul_assoc, mul_inv_cancel₀ hpi, one_mul]
  have hbdP : ∀ r ∈ Ioc (0 : ℝ) 1, ∑' ℓ, potTerm k G ℓ r ≤ MP := fun r hr => by
    rw [(hasSum_potTerm hG.continuous hr.1.le).tsum_eq]
    calc (2 * π : ℝ)⁻¹ * (∫ θ in (0 : ℝ)..2 * π,
            r * (potV k ((r : ℂ) * Complex.exp ((θ : ℂ) * I))
              * ‖G ((r : ℂ) * Complex.exp ((θ : ℂ) * I))‖ ^ 2))
        ≤ (2 * π)⁻¹ * (2 * π * MP) :=
          mul_le_mul_of_nonneg_left (density_bound (continuous_potVsq hG.continuous) hpnn hMPbd hr)
            (by positivity)
      _ = MP := by rw [← mul_assoc, inv_mul_cancel₀ hpi, one_mul]
  obtain ⟨_, hPsum, hPint⟩ := energy_eq (continuous_potVsq hG.continuous) hcircP
    (potTerm_measurable hG.continuous) (fun ℓ r hr => potTerm_nonneg G ℓ hr.1.le)
    (fun r hr => (hasSum_potTerm hG.continuous hr.1.le).summable)
    (lintegral_tsum_ofReal_ne_top (fun ℓ r hr => potTerm_nonneg G ℓ hr.1.le)
      (fun r hr => (hasSum_potTerm hG.continuous hr.1.le).summable) hbdP)
  refine (hDsum.sub hPsum).congr (fun ℓ => ?_)
  rw [← intervalIntegral.integral_sub (hDint ℓ) (hPint ℓ)]
  exact intervalIntegral.integral_congr (fun r _ => dirTerm_sub_potTerm G ℓ r)

end KsIndex.PiAssembly
