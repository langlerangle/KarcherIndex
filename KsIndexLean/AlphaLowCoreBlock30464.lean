module

public import KsIndexLean.AlphaLowModeSumAssembly
public import KsIndexLean.AlphaLowBlockCertificate30464

@[expose] public section

namespace KsIndex.AlphaRemarkTrial.Cache30464
theorem core_center (n : ℤ) :
    lowLinearNumerator (Finset.Ico (14079) (14335)) n =
      blockLinearNumerator (14079) n center := by
  apply (blockLinearNumerator_eq_core KsIndex.PositiveEnergyAlphaLowProd.valid
    (14079) n center ?_ ?_).symm
  · intro i
    convert low_block_covered 30464 256 (by norm_num) i using 1; norm_num
  · intro i
    simpa only [center, mode, show (-16385 : ℤ)+30464 = 14079 by norm_num] using (checked i).1

theorem core_radius (n : ℤ) :
    lowLinearRadius (Finset.Ico (14079) (14335)) n =
      blockLinearRadius (14079) n radius := by
  apply (blockLinearRadius_eq_core KsIndex.PositiveEnergyAlphaLowProd.valid
    (14079) n radius ?_ ?_).symm
  · intro i
    convert low_block_covered 30464 256 (by norm_num) i using 1; norm_num
  · intro i
    simpa only [radius, mode, show (-16385 : ℤ)+30464 = 14079 by norm_num] using (checked i).2
theorem core_m2 :
    lowLinearNumerator (Finset.Ico (14079) (14335)) (-2) = 103687338031012723455561543052582645217345295155 ∧
    lowLinearRadius (Finset.Ico (14079) (14335)) (-2) = 153534930034274820266810880454858353601 :=
  ⟨(core_center _).trans sum_m2.1, (core_radius _).trans sum_m2.2⟩
theorem core_m1 :
    lowLinearNumerator (Finset.Ico (14079) (14335)) (-1) = -103694636333457812258672428093553727116041066128 ∧
    lowLinearRadius (Finset.Ico (14079) (14335)) (-1) = 153545737005701535453195105511036449322 :=
  ⟨(core_center _).trans sum_m1.1, (core_radius _).trans sum_m1.2⟩
theorem core_p1 :
    lowLinearNumerator (Finset.Ico (14079) (14335)) (1) = -103709236021125158599325279069863020170296265806 ∧
    lowLinearRadius (Finset.Ico (14079) (14335)) (1) = 153567355513388622519101048996429573626 :=
  ⟨(core_center _).trans sum_p1.1, (core_radius _).trans sum_p1.2⟩
theorem core_p2 :
    lowLinearNumerator (Finset.Ico (14079) (14335)) (2) = 103716537406781509839037548246983474233764164101 ∧
    lowLinearRadius (Finset.Ico (14079) (14335)) (2) = 153578167050291781248900891554911928868 :=
  ⟨(core_center _).trans sum_p2.1, (core_radius _).trans sum_p2.2⟩
end KsIndex.AlphaRemarkTrial.Cache30464
