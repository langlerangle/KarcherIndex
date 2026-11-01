module

public import KsIndexLean.AlphaLowModeResidual
public import KsIndexLean.AlphaSignedWindowBudget

@[expose] public section


/-! A uniform four-mode residual bound suffices for the low-window energy allocation. -/
namespace KsIndex.AlphaRemarkTrial
open CircleQ AlphaResidual

theorem low_energy_of_uniform_bound
    (h : ∀ n ∈ residualWindow 2,
      |realResidual AlphaRemark.spectralUpper n| ≤ (1/2500 : ℝ)) :
    (∑ n ∈ residualWindow 2,
      realResidual AlphaRemark.spectralUpper n^2/residualWeight n) ≤
        (1/10000000 : ℝ) := by
  have he : residualWindow 2 = ({-2, -1, 1, 2} : Finset ℤ) := by
    ext n
    simp only [mem_residualWindow, abs_le, Finset.mem_insert, Finset.mem_singleton]
    omega
  calc
    _ ≤ ∑ n ∈ residualWindow 2, (1/2500 : ℝ)^2/residualWeight n := by
      apply Finset.sum_le_sum
      intro n hn
      apply div_le_div_of_nonneg_right _ (residualWeight_pos n).le
      simpa only [sq_abs] using
        (sq_le_sq₀ (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 1/2500)).mpr (h n hn)
    _ ≤ _ := by
      rw [he]
      norm_num [residualWeight, sigP]

theorem low_energy_of_center_bounds
    (h : ∀ n ∈ residualWindow 2,
      -(1/2500 : ℝ) ≤ lowResidualCenter n-lowResidualError n ∧
      lowResidualCenter n+lowResidualError n ≤ (1/2500 : ℝ)) :
    (∑ n ∈ residualWindow 2,
      realResidual AlphaRemark.spectralUpper n^2/residualWeight n) ≤
        (1/10000000 : ℝ) := by
  apply low_energy_of_uniform_bound
  intro n hn
  have hc := residualWindow_cut (by norm_num : 2 ≤ 16385) n hn
  have hb := abs_le.mp (realResidual_lowResidualCenter n hc)
  have hh := h n hn
  exact abs_le.mpr ⟨by linarith [hb.1, hh.1], by linarith [hb.2, hh.2]⟩

end KsIndex.AlphaRemarkTrial
