module

public import KsIndexLean.AlphaLowModeSumAssembly
public import KsIndexLean.AlphaLowBlockCertificate22784

@[expose] public section

namespace KsIndex.AlphaRemarkTrial.Cache22784
theorem core_center (n : ℤ) :
    lowLinearNumerator (Finset.Ico (6399) (6655)) n =
      blockLinearNumerator (6399) n center := by
  apply (blockLinearNumerator_eq_core KsIndex.PositiveEnergyAlphaLowProd.valid
    (6399) n center ?_ ?_).symm
  · intro i
    convert low_block_covered 22784 256 (by norm_num) i using 1; norm_num
  · intro i
    simpa only [center, mode, show (-16385 : ℤ)+22784 = 6399 by norm_num] using (checked i).1

theorem core_radius (n : ℤ) :
    lowLinearRadius (Finset.Ico (6399) (6655)) n =
      blockLinearRadius (6399) n radius := by
  apply (blockLinearRadius_eq_core KsIndex.PositiveEnergyAlphaLowProd.valid
    (6399) n radius ?_ ?_).symm
  · intro i
    convert low_block_covered 22784 256 (by norm_num) i using 1; norm_num
  · intro i
    simpa only [radius, mode, show (-16385 : ℤ)+22784 = 6399 by norm_num] using (checked i).2
theorem core_m2 :
    lowLinearNumerator (Finset.Ico (6399) (6655)) (-2) = 326961644885341972746210747128058527249495423058 ∧
    lowLinearRadius (Finset.Ico (6399) (6655)) (-2) = 506229920307501685727334864183967994173 :=
  ⟨(core_center _).trans sum_m2.1, (core_radius _).trans sum_m2.2⟩
theorem core_m1 :
    lowLinearNumerator (Finset.Ico (6399) (6655)) (-1) = -327011746833277052777659579905070241959484400084 ∧
    lowLinearRadius (Finset.Ico (6399) (6655)) (-1) = 506307492986509234818463801870650609242 :=
  ⟨(core_center _).trans sum_m1.1, (core_radius _).trans sum_m1.2⟩
theorem core_p1 :
    lowLinearNumerator (Finset.Ico (6399) (6655)) (1) = -327111996813392220784717856834565477327137449311 ∧
    lowLinearRadius (Finset.Ico (6399) (6655)) (1) = 506462709697129506825538257593252598289 :=
  ⟨(core_center _).trans sum_p1.1, (core_radius _).trans sum_p1.2⟩
theorem core_p2 :
    lowLinearNumerator (Finset.Ico (6399) (6655)) (2) = 327162144859705862217927094613595347538577119047 ∧
    lowLinearRadius (Finset.Ico (6399) (6655)) (2) = 506540353750625483736894451500051292439 :=
  ⟨(core_center _).trans sum_p2.1, (core_radius _).trans sum_p2.2⟩
end KsIndex.AlphaRemarkTrial.Cache22784
