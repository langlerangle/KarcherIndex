module

public import KsIndexLean.ProtoWindowGlue
public import KsIndexLean.ProtoTailPp
public import KsIndexLean.ProtoTailPn
public import KsIndexLean.ProtoTailMp
public import KsIndexLean.ProtoTailMn

@[expose] public section

/-! Mini-assembly: the circle form at spectralLower is at most one explicit
rational (POSITIVE at M = 64; no sign is asserted — this validates the chain). -/
set_option maxHeartbeats 1000000
namespace KsIndex.NegSignProto
open KsIndex.AlphaRemarkTrial CircleQ

theorem qform_le_grand :
    Qform KsIndex.AlphaRemark.spectralLower trial ≤ ((779377616873154288340378386988122842177161546788025944295814883927680338515659717564102351282911138930490942276279219050182264877187991329473701960648200189377 / 199001616964234995745957768114218750000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ) : ℝ) := by
  have hA := qform_trial_le_window_add_tails KsIndex.AlphaRemark.spectralLower 64 (by norm_num)
  have hIcc : (Finset.Icc (-(64 : ℕ) : ℤ) (64 : ℕ)) = window := by
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
  have ePp : (fun i => ((2 * (64 : ℕ) + 2 + shift i : ℤ) : ℝ)) = rPp := by
    funext i; fin_cases i <;> norm_num [rPp, kPp, shift]
  have ePn : (fun i => ((2 * (64 : ℕ) + 2 - shift i : ℤ) : ℝ)) = rPn := by
    funext i; fin_cases i <;> norm_num [rPn, kPn, shift]
  have eMp : (fun i => ((2 * (64 : ℕ) + 3 + shift i : ℤ) : ℝ)) = rMp := by
    funext i; fin_cases i <;> norm_num [rMp, kMp, shift]
  have eMn : (fun i => ((2 * (64 : ℕ) + 1 - shift i : ℤ) : ℝ)) = rMn := by
    funext i; fin_cases i <;> norm_num [rMn, kMn, shift]
  rw [ePp, ePn, eMp, eMn] at hA
  have c1 : (6 * ((64 : ℕ) : ℝ) + 7) = ((391 : ℚ) : ℝ) := by norm_num
  have c2 : (6 * ((64 : ℕ) : ℝ) + 5) = ((389 : ℚ) : ℝ) := by norm_num
  have c3 : (6 * ((64 : ℕ) : ℝ) + 10) = ((394 : ℚ) : ℝ) := by norm_num
  have c4 : (6 * ((64 : ℕ) : ℝ) + 2) = ((386 : ℚ) : ℝ) := by norm_num
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
  have hTM : ((tailLeading rMp + tailError rMp ((394 : ℚ) : ℝ))
      + (tailLeading rMn + tailError rMn ((386 : ℚ) : ℝ)))
      ≤ ((1396552188348133580671844257187109957098247407166989264183004554216253215288334586566396771910736925443638192690334731560712891583008618218694601 / 241214081168769691813282143168750000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ) : ℝ) := by
    have he : ((tailLeadingUpperQ cenMp radMp : ℚ) : ℝ) = ((tailLeadingUpperQ cenMp radMp : ℚ) : ℝ) := rfl
    push_cast at hlMp heMp hlMn heMn ⊢
    linarith
  have hTMs := mul_le_mul_of_nonneg_left hTM
    (sq_nonneg KsIndex.AlphaRemark.spectralLower)
  have hfinal : ((-16455583780620473902026269186934053812416507089644783642273512289915069780094443862819369300268555622424272037871 / 1250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ) : ℝ)
      + ((tailLeading rPp + tailError rPp ((391 : ℚ) : ℝ))
        + (tailLeading rPn + tailError rPn ((389 : ℚ) : ℝ)))
      + KsIndex.AlphaRemark.spectralLower ^ 2 *
          ((1396552188348133580671844257187109957098247407166989264183004554216253215288334586566396771910736925443638192690334731560712891583008618218694601 / 241214081168769691813282143168750000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ) : ℝ)
      ≤ ((779377616873154288340378386988122842177161546788025944295814883927680338515659717564102351282911138930490942276279219050182264877187991329473701960648200189377 / 199001616964234995745957768114218750000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ) : ℝ) := by
    rw [KsIndex.AlphaRemark.spectralLower]
    push_cast at hlPp hePp hlPn hePn ⊢
    nlinarith [hlPp, hePp, hlPn, hePn]
  calc Qform KsIndex.AlphaRemark.spectralLower trial
      ≤ _ := hA
    _ ≤ _ := add_le_add (add_le_add hW (le_refl _)) (le_refl _)
    _ ≤ _ := add_le_add (le_refl _) hTMs
    _ ≤ _ := hfinal

end KsIndex.NegSignProto
