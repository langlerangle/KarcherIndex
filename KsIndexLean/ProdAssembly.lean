module

public import KsIndexLean.ProdWindowGlue
public import KsIndexLean.ProdTailPp
public import KsIndexLean.ProdTailPn
public import KsIndexLean.ProdTailMp
public import KsIndexLean.ProdTailMn

@[expose] public section

/-! Assembly of the finite-window and tail bounds at spectralLower.
The theorem bounds the trial circle form by an explicit rational at M = 8192.
Its sign is established separately by the consuming spectral-sign theorem. -/
set_option maxHeartbeats 1000000
namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial CircleQ

theorem qform_le_grand :
    Qform KsIndex.AlphaRemark.spectralLower trial ≤ ((-3385506737931039922658726158043093087910093679999687482862387117068840071309997856305741829160693730497499717499471105017979738691333761180865623355733839342688962795812825453389967 / 32096887956685492795889001744517162291741770613188849987543750000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ) : ℝ) := by
  have hA := qform_trial_le_window_add_tails KsIndex.AlphaRemark.spectralLower 8192 (by norm_num)
  have hIcc : (Finset.Icc (-(8192 : ℕ) : ℤ) (8192 : ℕ)) = window := by
    rw [window]; norm_num
  have hwP : (∑ n ∈ window, sigP n * sample (2 * n) ^ 2)
      = ∑ n ∈ window, sigP n * ‖trial n‖ ^ 2 :=
    Finset.sum_congr rfl fun n _ => by
      rw [trial_eq_sample, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  have hwM : (∑ m ∈ window, sigM m * sample (2 * m + 1) ^ 2)
      = ∑ m ∈ window, sigM m * ‖convS trial m‖ ^ 2 :=
    Finset.sum_congr rfl fun m _ => by
      rw [convS_eq_sample, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  rw [hIcc, hwP, hwM] at hA
  have ePp : (fun i => ((2 * (8192 : ℕ) + 2 + shift i : ℤ) : ℝ)) = rPp := by
    funext i; fin_cases i <;> norm_num [rPp, kPp, shift]
  have ePn : (fun i => ((2 * (8192 : ℕ) + 2 - shift i : ℤ) : ℝ)) = rPn := by
    funext i; fin_cases i <;> norm_num [rPn, kPn, shift]
  have eMp : (fun i => ((2 * (8192 : ℕ) + 3 + shift i : ℤ) : ℝ)) = rMp := by
    funext i; fin_cases i <;> norm_num [rMp, kMp, shift]
  have eMn : (fun i => ((2 * (8192 : ℕ) + 1 - shift i : ℤ) : ℝ)) = rMn := by
    funext i; fin_cases i <;> norm_num [rMn, kMn, shift]
  rw [ePp, ePn, eMp, eMn] at hA
  have c1 : (6 * ((8192 : ℕ) : ℝ) + 7) = ((49159 : ℚ) : ℝ) := by norm_num
  have c2 : (6 * ((8192 : ℕ) : ℝ) + 5) = ((49157 : ℚ) : ℝ) := by norm_num
  have c3 : (6 * ((8192 : ℕ) : ℝ) + 10) = ((49162 : ℚ) : ℝ) := by norm_num
  have c4 : (6 * ((8192 : ℕ) : ℝ) + 2) = ((49154 : ℚ) : ℝ) := by norm_num
  rw [c1, c2, c3, c4] at hA
  have hlPp := leadPp; have hePp := errPp
  have hlPn := leadPn; have hePn := errPn
  have hlMp := leadMp; have heMp := errMp
  have hlMn := leadMn; have heMn := errMn
  rw [leadValPp] at hlPp; rw [errValPp] at hePp
  rw [leadValPn] at hlPn; rw [errValPn] at hePn
  rw [leadValMp] at hlMp; rw [errValMp] at heMp
  rw [leadValMn] at hlMn; rw [errValMn] at heMn
  have hW := window_bound
  have hTM : ((tailLeading rMp + tailError rMp ((49162 : ℚ) : ℝ))
      + (tailLeading rMn + tailError rMn ((49154 : ℚ) : ℝ)))
      ≤ ((647421487606089297712988881286166529453197213536749162304221817765984579219885583560133902985471999597053254214906914894854773870194744124241052489237826773024407071908627 / 14122630700941616830191160767587551408366379069803093994519250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ) : ℝ) := by
    have he : ((tailLeadingUpperQ cenMp radMp : ℚ) : ℝ) = ((tailLeadingUpperQ cenMp radMp : ℚ) : ℝ) := rfl
    push_cast at hlMp heMp hlMn heMn ⊢
    linarith
  have hTMs := mul_le_mul_of_nonneg_left hTM
    (sq_nonneg KsIndex.AlphaRemark.spectralLower)
  have hfinal : ((-3519479587205274334899401480494021213438316130810164589521290648844765544684289309438402175793188353950775886959 / 25000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ) : ℝ)
      + ((tailLeading rPp + tailError rPp ((49159 : ℚ) : ℝ))
        + (tailLeading rPn + tailError rPn ((49157 : ℚ) : ℝ)))
      + KsIndex.AlphaRemark.spectralLower ^ 2 *
          ((647421487606089297712988881286166529453197213536749162304221817765984579219885583560133902985471999597053254214906914894854773870194744124241052489237826773024407071908627 / 14122630700941616830191160767587551408366379069803093994519250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ) : ℝ)
      ≤ ((-3385506737931039922658726158043093087910093679999687482862387117068840071309997856305741829160693730497499717499471105017979738691333761180865623355733839342688962795812825453389967 / 32096887956685492795889001744517162291741770613188849987543750000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ) : ℝ) := by
    rw [KsIndex.AlphaRemark.spectralLower]
    push_cast at hlPp hePp hlPn hePn ⊢
    nlinarith [hlPp, hePp, hlPn, hePn]
  calc Qform KsIndex.AlphaRemark.spectralLower trial
      ≤ _ := hA
    _ ≤ _ := add_le_add (add_le_add hW (le_refl _)) (le_refl _)
    _ ≤ _ := add_le_add (le_refl _) hTMs
    _ ≤ _ := hfinal

end KsIndex.NegSignProd
