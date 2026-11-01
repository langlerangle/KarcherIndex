module

public import KsIndexLean.AlphaLowModeSumAssembly
public import KsIndexLean.AlphaLowBlockCertificate24320

@[expose] public section

namespace KsIndex.AlphaRemarkTrial.Cache24320
theorem core_center (n : ℤ) :
    lowLinearNumerator (Finset.Ico (7935) (8191)) n =
      blockLinearNumerator (7935) n center := by
  apply (blockLinearNumerator_eq_core KsIndex.PositiveEnergyAlphaLowProd.valid
    (7935) n center ?_ ?_).symm
  · intro i
    convert low_block_covered 24320 256 (by norm_num) i using 1; norm_num
  · intro i
    simpa only [center, mode, show (-16385 : ℤ)+24320 = 7935 by norm_num] using (checked i).1

theorem core_radius (n : ℤ) :
    lowLinearRadius (Finset.Ico (7935) (8191)) n =
      blockLinearRadius (7935) n radius := by
  apply (blockLinearRadius_eq_core KsIndex.PositiveEnergyAlphaLowProd.valid
    (7935) n radius ?_ ?_).symm
  · intro i
    convert low_block_covered 24320 256 (by norm_num) i using 1; norm_num
  · intro i
    simpa only [radius, mode, show (-16385 : ℤ)+24320 = 7935 by norm_num] using (checked i).2
theorem core_m2 :
    lowLinearNumerator (Finset.Ico (7935) (8191)) (-2) = 239254417295956693544463706740687865248742760701 ∧
    lowLinearRadius (Finset.Ico (7935) (8191)) (-2) = 365984292752324684027921105824121370576 :=
  ⟨(core_center _).trans sum_m2.1, (core_radius _).trans sum_m2.2⟩
theorem core_m1 :
    lowLinearNumerator (Finset.Ico (7935) (8191)) (-1) = -239284092916519926256156302425777923006555851028 ∧
    lowLinearRadius (Finset.Ico (7935) (8191)) (-1) = 366029687371742688444126384151489608323 :=
  ⟨(core_center _).trans sum_m1.1, (core_radius _).trans sum_m1.2⟩
theorem core_p1 :
    lowLinearNumerator (Finset.Ico (7935) (8191)) (1) = -239343466249652036306102354346527840734933299038 ∧
    lowLinearRadius (Finset.Ico (7935) (8191)) (1) = 366120510404750178536681394011390704835 :=
  ⟨(core_center _).trans sum_p1.1, (core_radius _).trans sum_p1.2⟩
theorem core_p2 :
    lowLinearNumerator (Finset.Ico (7935) (8191)) (2) = 239373163967704183377681348072976289234561109771 ∧
    lowLinearRadius (Finset.Ico (7935) (8191)) (2) = 366165938826727469803905400652995370792 :=
  ⟨(core_center _).trans sum_p2.1, (core_radius _).trans sum_p2.2⟩
end KsIndex.AlphaRemarkTrial.Cache24320
