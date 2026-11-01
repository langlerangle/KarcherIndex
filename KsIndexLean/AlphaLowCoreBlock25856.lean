module

public import KsIndexLean.AlphaLowModeSumAssembly
public import KsIndexLean.AlphaLowBlockCertificate25856

@[expose] public section

namespace KsIndex.AlphaRemarkTrial.Cache25856
theorem core_center (n : ℤ) :
    lowLinearNumerator (Finset.Ico (9471) (9727)) n =
      blockLinearNumerator (9471) n center := by
  apply (blockLinearNumerator_eq_core KsIndex.PositiveEnergyAlphaLowProd.valid
    (9471) n center ?_ ?_).symm
  · intro i
    convert low_block_covered 25856 256 (by norm_num) i using 1; norm_num
  · intro i
    simpa only [center, mode, show (-16385 : ℤ)+25856 = 9471 by norm_num] using (checked i).1

theorem core_radius (n : ℤ) :
    lowLinearRadius (Finset.Ico (9471) (9727)) n =
      blockLinearRadius (9471) n radius := by
  apply (blockLinearRadius_eq_core KsIndex.PositiveEnergyAlphaLowProd.valid
    (9471) n radius ?_ ?_).symm
  · intro i
    convert low_block_covered 25856 256 (by norm_num) i using 1; norm_num
  · intro i
    simpa only [radius, mode, show (-16385 : ℤ)+25856 = 9471 by norm_num] using (checked i).2
theorem core_m2 :
    lowLinearNumerator (Finset.Ico (9471) (9727)) (-2) = 184931994954520017390271781632396464189040695266 ∧
    lowLinearRadius (Finset.Ico (9471) (9727)) (-2) = 280075583840476999086221875992302524823 :=
  ⟨(core_center _).trans sum_m2.1, (core_radius _).trans sum_m2.2⟩
theorem core_m1 :
    lowLinearNumerator (Finset.Ico (9471) (9727)) (-1) = -184951261531495768926066041849816054204114452532 ∧
    lowLinearRadius (Finset.Ico (9471) (9727)) (-1) = 280104762761807361821753752364864921206 :=
  ⟨(core_center _).trans sum_m1.1, (core_radius _).trans sum_m1.2⟩
theorem core_p1 :
    lowLinearNumerator (Finset.Ico (9471) (9727)) (1) = -184989806732049421242097537838855534115328739156 ∧
    lowLinearRadius (Finset.Ico (9471) (9727)) (1) = 280163138848915529798817706096538768581 :=
  ⟨(core_center _).trans sum_p1.1, (core_radius _).trans sum_p1.2⟩
theorem core_p2 :
    lowLinearNumerator (Finset.Ico (9471) (9727)) (2) = 185009085358138481690724929832866372163016427233 ∧
    lowLinearRadius (Finset.Ico (9471) (9727)) (2) = 280192336018496471868062337607199416181 :=
  ⟨(core_center _).trans sum_p2.1, (core_radius _).trans sum_p2.2⟩
end KsIndex.AlphaRemarkTrial.Cache25856
