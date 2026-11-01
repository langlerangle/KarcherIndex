module

/-
Value bound for a finite-mode witness on an interior collar.

For `k ≥ 3`, `1 ≤ r ≤ k−1`, `η > 0`, and a point satisfying
`1−2δ ≤ ‖w‖² < 1` with `1−2δ > 0`, the theorem bounds `Psi` by three terms:

  `2δ / (2 * sqrt(1−2δ) * (1−cos d))`
  `+ Σ_{n ∉ [-N,N]} ‖fc (psiF η) n‖`
  `+ kap k * (2k−2) * 2δ * Σ_n ‖fc (psiF η) n‖`.

The angular margin `0 < d ≤ π` is supplied as a hypothesis at the chosen point:
for every angle where `fInf` is nonzero, `cos(arg w − φ) ≤ cos d`.
This file does not construct a margin independent of the collar width or choose
a coupled limit of `δ` and `N`. Apart from the coefficient tail, the displayed
right-hand side is independent of `N`, with its dependence on `δ`, `d` and `η`
retained explicitly. The inhabited collar forces `δ > 0` even though that is not
a separate hypothesis.

The proof splits `Psi` into its harmonic and correction parts, applies the
Poisson margin estimate and truncation bound to the former, and bounds the
latter by the full summable coefficient mass. This is a value bound, not a
gradient or cutoff-energy estimate.
-/
public import KsIndexLean.ModeSeries
public import KsIndexLean.ModeCorr
public import KsIndexLean.ModeGrad

@[expose] public section


noncomputable section

open Real Set Complex
open KsIndex.ArcField KsIndex.ArcPoisson KsIndex.ArcInfCoeff KsIndex.ModeWitness
  KsIndex.ModePoisson KsIndex.ModeCorr KsIndex.ModeSeries KsIndex.ModeGrad
  KsIndex.Radial KsIndex.SingleDisk

namespace KsIndex.CollarValue

variable {k r : ℕ}

/-- Explicit collar value bound under a supplied angular margin. The first and third
terms are independent of `N`; the second is the coefficient tail outside `[-N,N]`. -/
theorem collar_value_bound (hk : 3 ≤ k) (hr1 : 1 ≤ r) (hrk : r ≤ k - 1)
    {η δ : ℝ} (hη0 : 0 < η) (hδpos : 0 < 1 - 2 * δ) (N : ℕ)
    {d : ℝ} (hd0 : 0 < d) (hdπ : d ≤ π)
    {w : ℂ} (hwlow : 1 - 2 * δ ≤ ‖w‖ ^ 2) (hw1 : ‖w‖ < 1)
    (hmargin : ∀ φ, fInf k r η φ ≠ 0 → Real.cos (Complex.arg w - φ) ≤ Real.cos d) :
    ‖Psi k r N (Parseval.fc (psiF η)) w‖
      ≤ 2 * δ / (2 * Real.sqrt (1 - 2 * δ) * (1 - Real.cos d))
        + (∑' n : ((↑(Finset.Icc (-(N : ℤ)) (N : ℤ)) : Set ℤ)ᶜ : Set ℤ),
            ‖Parseval.fc (psiF η) (n : ℤ)‖)
        + kap k * (2 * (k : ℝ) - 2) * (2 * δ)
          * (∑' n : ℤ, ‖Parseval.fc (psiF η) n‖) := by
  have hk2 : 2 ≤ k := by omega
  have hw0 : 0 < ‖w‖ := by nlinarith [norm_nonneg w]
  have hwle : ‖w‖ ≤ 1 := hw1.le
  have hcos1 : Real.cos d < 1 := cos_lt_one_of_pos_le_pi hd0 hdπ
  have hcosd : 0 < 1 - Real.cos d := by linarith
  have hsq : Real.sqrt (1 - 2 * δ) ≤ ‖w‖ := by
    have h := Real.sqrt_le_sqrt hwlow
    rwa [Real.sqrt_sq (norm_nonneg w)] at h
  have hsqpos : 0 < Real.sqrt (1 - 2 * δ) := Real.sqrt_pos.mpr hδpos
  have hnum : 1 - ‖w‖ ^ 2 ≤ 2 * δ := by linarith
  have hnum0 : 0 ≤ 1 - ‖w‖ ^ 2 := by nlinarith
  have h1w : 1 - ‖w‖ ≤ 2 * δ := by nlinarith [norm_nonneg w]
  have hδ0 : 0 < 2 * δ := lt_of_lt_of_le (by linarith : (0 : ℝ) < 1 - ‖w‖) h1w
  -- (ii) the Poisson value bound, simplified to the collar constant
  have hPB : ‖poissonExt (fInf k r η) w‖
      ≤ 2 * δ / (2 * Real.sqrt (1 - 2 * δ) * (1 - Real.cos d)) := by
    have h0 := norm_poissonExt_le (continuous_fInf k r η) hd0 hdπ hw0 hw1 hmargin
    have hL1 : (∫ φ in (0:ℝ)..2 * π, ‖fInf k r η φ‖) ≤ 2 * π := by
      calc (∫ φ in (0:ℝ)..2 * π, ‖fInf k r η φ‖)
          ≤ ∫ _ in (0:ℝ)..2 * π, (1 : ℝ) :=
            intervalIntegral.integral_mono_on (by positivity)
              ((continuous_fInf k r η).norm.intervalIntegrable _ _)
              intervalIntegrable_const (fun φ _ => norm_fInf_le_one k r η φ)
        _ = 2 * π := by simp
    have hXnn : 0 ≤ (2 * π)⁻¹ * ((1 - ‖w‖ ^ 2) / (2 * ‖w‖ * (1 - Real.cos d))) := by
      have hden : 0 < 2 * ‖w‖ * (1 - Real.cos d) := by positivity
      positivity
    calc ‖poissonExt (fInf k r η) w‖
        ≤ (2 * π)⁻¹ * ((1 - ‖w‖ ^ 2) / (2 * ‖w‖ * (1 - Real.cos d))) * (2 * π) :=
          le_trans h0 (mul_le_mul_of_nonneg_left hL1 hXnn)
      _ = (1 - ‖w‖ ^ 2) / (2 * ‖w‖ * (1 - Real.cos d)) := by
          rw [mul_comm ((2 * π)⁻¹) ((1 - ‖w‖ ^ 2) / (2 * ‖w‖ * (1 - Real.cos d))),
            mul_assoc, inv_mul_cancel₀ (by positivity : (2 * π : ℝ) ≠ 0), mul_one]
      _ ≤ 2 * δ / (2 * Real.sqrt (1 - 2 * δ) * (1 - Real.cos d)) := by
          have hden' : 0 < 2 * Real.sqrt (1 - 2 * δ) * (1 - Real.cos d) := by positivity
          have hdenle : 2 * Real.sqrt (1 - 2 * δ) * (1 - Real.cos d)
              ≤ 2 * ‖w‖ * (1 - Real.cos d) := by
            have := mul_le_mul_of_nonneg_left hsq (by norm_num : (0:ℝ) ≤ 2)
            exact mul_le_mul_of_nonneg_right this hcosd.le
          calc (1 - ‖w‖ ^ 2) / (2 * ‖w‖ * (1 - Real.cos d))
              ≤ (2 * δ) / (2 * ‖w‖ * (1 - Real.cos d)) := by
                have hdenw : 0 < 2 * ‖w‖ * (1 - Real.cos d) := by positivity
                exact div_le_div_of_nonneg_right hnum hdenw.le
            _ ≤ 2 * δ / (2 * Real.sqrt (1 - 2 * δ) * (1 - Real.cos d)) :=
                div_le_div_of_nonneg_left hδ0.le hden' hdenle
  -- (i) the harmonic part through the honest Poisson extension
  have hHtri : ‖Hpart k r N (Parseval.fc (psiF η)) w‖
      ≤ ‖poissonExt (fInf k r η) w‖
        + ‖poissonExt (fInf k r η) w - Hpart k r N (Parseval.fc (psiF η)) w‖ := by
    calc ‖Hpart k r N (Parseval.fc (psiF η)) w‖
        = ‖poissonExt (fInf k r η) w
            - (poissonExt (fInf k r η) w - Hpart k r N (Parseval.fc (psiF η)) w)‖ := by
          congr 1
          ring
      _ ≤ _ := norm_sub_le _ _
  have hH : ‖Hpart k r N (Parseval.fc (psiF η)) w‖
      ≤ 2 * δ / (2 * Real.sqrt (1 - 2 * δ) * (1 - Real.cos d))
        + (∑' n : ((↑(Finset.Icc (-(N : ℤ)) (N : ℤ)) : Set ℤ)ᶜ : Set ℤ),
            ‖Parseval.fc (psiF η) (n : ℤ)‖) :=
    le_trans hHtri (add_le_add hPB (norm_poissonExt_fInf_sub_Hpart hk hη0 N hw1))
  -- (iii) the correction part
  have hC : ‖((groundR k w : ℝ) : ℂ) * Gpart k r N (Parseval.fc (psiF η)) w‖
      ≤ kap k * (2 * (k : ℝ) - 2) * (2 * δ)
        * (∑' n : ℤ, ‖Parseval.fc (psiF η) n‖) := by
    have h1 := norm_correction_le hk hr1 hrk N (Parseval.fc (psiF η)) hwle
    have h3 : (∑ i : Fin (2 * N + 1), ‖Parseval.fc (psiF η) (slot N i)‖)
        ≤ ∑' n : ℤ, ‖Parseval.fc (psiF η) n‖ := by
      rw [sum_slot_eq_Icc N (fun n => ‖Parseval.fc (psiF η) n‖)]
      exact Summable.sum_le_tsum _ (fun n _ => norm_nonneg _)
        (KsIndex.ArcSmooth.summable_fc_psiF η hη0)
    have hκnn : 0 ≤ kap k * (2 * (k : ℝ) - 2) := by
      have hκ := kap_pos hk2
      have h2k : (2 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk2
      nlinarith
    have hfinnn : 0 ≤ ∑ i : Fin (2 * N + 1), ‖Parseval.fc (psiF η) (slot N i)‖ :=
      Finset.sum_nonneg (fun i _ => norm_nonneg _)
    calc ‖((groundR k w : ℝ) : ℂ) * Gpart k r N (Parseval.fc (psiF η)) w‖
        ≤ kap k * (2 * (k : ℝ) - 2) * (1 - ‖w‖)
            * ∑ i : Fin (2 * N + 1), ‖Parseval.fc (psiF η) (slot N i)‖ := h1
      _ ≤ kap k * (2 * (k : ℝ) - 2) * (2 * δ)
            * (∑' n : ℤ, ‖Parseval.fc (psiF η) n‖) := by
          refine mul_le_mul (mul_le_mul_of_nonneg_left h1w hκnn) h3 hfinnn ?_
          exact mul_nonneg hκnn hδ0.le
  -- assemble via the decomposition
  calc ‖Psi k r N (Parseval.fc (psiF η)) w‖
      = ‖Hpart k r N (Parseval.fc (psiF η)) w
          + ((groundR k w : ℝ) : ℂ) * Gpart k r N (Parseval.fc (psiF η)) w‖ := by
        rw [Psi_decomp hk hr1 hrk N _ w]
    _ ≤ ‖Hpart k r N (Parseval.fc (psiF η)) w‖
        + ‖((groundR k w : ℝ) : ℂ) * Gpart k r N (Parseval.fc (psiF η)) w‖ :=
        norm_add_le _ _
    _ ≤ (2 * δ / (2 * Real.sqrt (1 - 2 * δ) * (1 - Real.cos d))
          + (∑' n : ((↑(Finset.Icc (-(N : ℤ)) (N : ℤ)) : Set ℤ)ᶜ : Set ℤ),
              ‖Parseval.fc (psiF η) (n : ℤ)‖))
        + kap k * (2 * (k : ℝ) - 2) * (2 * δ)
          * (∑' n : ℤ, ‖Parseval.fc (psiF η) n‖) := add_le_add hH hC

end KsIndex.CollarValue
