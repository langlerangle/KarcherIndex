module

public import KsIndexLean.AlphaLowModeSumAssembly
public import KsIndexLean.AlphaLowBlockCertificate20992

@[expose] public section

namespace KsIndex.AlphaRemarkTrial.Cache20992
theorem core_center (n : ℤ) :
    lowLinearNumerator (Finset.Ico (4607) (4863)) n =
      blockLinearNumerator (4607) n center := by
  apply (blockLinearNumerator_eq_core KsIndex.PositiveEnergyAlphaLowProd.valid
    (4607) n center ?_ ?_).symm
  · intro i
    convert low_block_covered 20992 256 (by norm_num) i using 1; norm_num
  · intro i
    simpa only [center, mode, show (-16385 : ℤ)+20992 = 4607 by norm_num] using (checked i).1

theorem core_radius (n : ℤ) :
    lowLinearRadius (Finset.Ico (4607) (4863)) n =
      blockLinearRadius (4607) n radius := by
  apply (blockLinearRadius_eq_core KsIndex.PositiveEnergyAlphaLowProd.valid
    (4607) n radius ?_ ?_).symm
  · intro i
    convert low_block_covered 20992 256 (by norm_num) i using 1; norm_num
  · intro i
    simpa only [radius, mode, show (-16385 : ℤ)+20992 = 4607 by norm_num] using (checked i).2
theorem core_m2 :
    lowLinearNumerator (Finset.Ico (4607) (4863)) (-2) = 525618675440273506133132927861736483217847210618 ∧
    lowLinearRadius (Finset.Ico (4607) (4863)) (-2) = 828835214346137605193947335404430552589 :=
  ⟨(core_center _).trans sum_m2.1, (core_radius _).trans sum_m2.2⟩
theorem core_m1 :
    lowLinearNumerator (Finset.Ico (4607) (4863)) (-1) = -525729726157709914983175677228635485109948582907 ∧
    lowLinearRadius (Finset.Ico (4607) (4863)) (-1) = 829010329927045058914466544842460365345 :=
  ⟨(core_center _).trans sum_m1.1, (core_radius _).trans sum_m1.2⟩
theorem core_p1 :
    lowLinearNumerator (Finset.Ico (4607) (4863)) (1) = -525951968460663939348366497859507934372601952804 ∧
    lowLinearRadius (Finset.Ico (4607) (4863)) (1) = 829360783226438270692928472880849661894 :=
  ⟨(core_center _).trans sum_p1.1, (core_radius _).trans sum_p1.2⟩
theorem core_p2 :
    lowLinearNumerator (Finset.Ico (4607) (4863)) (2) = 526063160105772494446565440280218919389564417377 ∧
    lowLinearRadius (Finset.Ico (4607) (4863)) (2) = 829536121038895424472626706775283533514 :=
  ⟨(core_center _).trans sum_p2.1, (core_radius _).trans sum_p2.2⟩
end KsIndex.AlphaRemarkTrial.Cache20992
