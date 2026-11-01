module

public import KsIndexLean.AlphaLowModeSumAssembly
public import KsIndexLean.AlphaLowBlockCertificate20480

@[expose] public section

namespace KsIndex.AlphaRemarkTrial.Cache20480
theorem core_center (n : ℤ) :
    lowLinearNumerator (Finset.Ico (4095) (4351)) n =
      blockLinearNumerator (4095) n center := by
  apply (blockLinearNumerator_eq_core KsIndex.PositiveEnergyAlphaLowProd.valid
    (4095) n center ?_ ?_).symm
  · intro i
    convert low_block_covered 20480 256 (by norm_num) i using 1; norm_num
  · intro i
    simpa only [center, mode, show (-16385 : ℤ)+20480 = 4095 by norm_num] using (checked i).1

theorem core_radius (n : ℤ) :
    lowLinearRadius (Finset.Ico (4095) (4351)) n =
      blockLinearRadius (4095) n radius := by
  apply (blockLinearRadius_eq_core KsIndex.PositiveEnergyAlphaLowProd.valid
    (4095) n radius ?_ ?_).symm
  · intro i
    convert low_block_covered 20480 256 (by norm_num) i using 1; norm_num
  · intro i
    simpa only [radius, mode, show (-16385 : ℤ)+20480 = 4095 by norm_num] using (checked i).2
theorem core_m2 :
    lowLinearNumerator (Finset.Ico (4095) (4351)) (-2) = 622639691412002695578747173491742035101388155321 ∧
    lowLinearRadius (Finset.Ico (4095) (4351)) (-2) = 988233832440479100545856417509027087587 :=
  ⟨(core_center _).trans sum_m2.1, (core_radius _).trans sum_m2.2⟩
theorem core_m1 :
    lowLinearNumerator (Finset.Ico (4095) (4351)) (-1) = -622787208624428239230979042127335447677123854014 ∧
    lowLinearRadius (Finset.Ico (4095) (4351)) (-1) = 988467971117715010795026138776978151735 :=
  ⟨(core_center _).trans sum_m1.1, (core_radius _).trans sum_m1.2⟩
theorem core_p1 :
    lowLinearNumerator (Finset.Ico (4095) (4351)) (1) = -623082452913673001758506281154108408012781203340 ∧
    lowLinearRadius (Finset.Ico (4095) (4351)) (1) = 988936581573827111975932299402112532754 :=
  ⟨(core_center _).trans sum_p1.1, (core_radius _).trans sum_p1.2⟩
theorem core_p2 :
    lowLinearNumerator (Finset.Ico (4095) (4351)) (2) = 623230180090067057728597524195836400980557293600 ∧
    lowLinearRadius (Finset.Ico (4095) (4351)) (2) = 989171053510753541842909020543950468256 :=
  ⟨(core_center _).trans sum_p2.1, (core_radius _).trans sum_p2.2⟩
end KsIndex.AlphaRemarkTrial.Cache20480
