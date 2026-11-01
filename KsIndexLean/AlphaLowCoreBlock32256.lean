module

public import KsIndexLean.AlphaLowModeSumAssembly
public import KsIndexLean.AlphaLowBlockCertificate32256

@[expose] public section

namespace KsIndex.AlphaRemarkTrial.Cache32256
theorem core_center (n : ℤ) :
    lowLinearNumerator (Finset.Ico (15871) (16127)) n =
      blockLinearNumerator (15871) n center := by
  apply (blockLinearNumerator_eq_core KsIndex.PositiveEnergyAlphaLowProd.valid
    (15871) n center ?_ ?_).symm
  · intro i
    convert low_block_covered 32256 256 (by norm_num) i using 1; norm_num
  · intro i
    simpa only [center, mode, show (-16385 : ℤ)+32256 = 15871 by norm_num] using (checked i).1

theorem core_radius (n : ℤ) :
    lowLinearRadius (Finset.Ico (15871) (16127)) n =
      blockLinearRadius (15871) n radius := by
  apply (blockLinearRadius_eq_core KsIndex.PositiveEnergyAlphaLowProd.valid
    (15871) n radius ?_ ?_).symm
  · intro i
    convert low_block_covered 32256 256 (by norm_num) i using 1; norm_num
  · intro i
    simpa only [radius, mode, show (-16385 : ℤ)+32256 = 15871 by norm_num] using (checked i).2
theorem core_m2 :
    lowLinearNumerator (Finset.Ico (15871) (16127)) (-2) = 87025026699146679418271873439156309937717329753 ∧
    lowLinearRadius (Finset.Ico (15871) (16127)) (-2) = 127984165682072562149793252104002917738 :=
  ⟨(core_center _).trans sum_m2.1, (core_radius _).trans sum_m2.2⟩
theorem core_m1 :
    lowLinearNumerator (Finset.Ico (15871) (16127)) (-1) = -87030466050452980456074368429691877525753379288 ∧
    lowLinearRadius (Finset.Ico (15871) (16127)) (-1) = 127992165124535315985101257308850228505 :=
  ⟨(core_center _).trans sum_m1.1, (core_radius _).trans sum_m1.2⟩
theorem core_p1 :
    lowLinearNumerator (Finset.Ico (15871) (16127)) (1) = -87041346793228566860571814354495104178274432908 ∧
    lowLinearRadius (Finset.Ico (15871) (16127)) (1) = 128008167009852880947756364809162028007 :=
  ⟨(core_center _).trans sum_p1.1, (core_radius _).trans sum_p1.2⟩
theorem core_p2 :
    lowLinearNumerator (Finset.Ico (15871) (16127)) (2) = 87046788184952944780768194705933974583958116108 ∧
    lowLinearRadius (Finset.Ico (15871) (16127)) (2) = 128016169453082847696249367133820528481 :=
  ⟨(core_center _).trans sum_p2.1, (core_radius _).trans sum_p2.2⟩
end KsIndex.AlphaRemarkTrial.Cache32256
