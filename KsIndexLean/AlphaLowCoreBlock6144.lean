module

public import KsIndexLean.AlphaLowModeSumAssembly
public import KsIndexLean.AlphaLowBlockCertificate6144

@[expose] public section

namespace KsIndex.AlphaRemarkTrial.Cache6144
theorem core_center (n : ℤ) :
    lowLinearNumerator (Finset.Ico (-10241) (-9985)) n =
      blockLinearNumerator (-10241) n center := by
  apply (blockLinearNumerator_eq_core KsIndex.PositiveEnergyAlphaLowProd.valid
    (-10241) n center ?_ ?_).symm
  · intro i
    convert low_block_covered 6144 256 (by norm_num) i using 1; norm_num
  · intro i
    simpa only [center, mode, show (-16385 : ℤ)+6144 = -10241 by norm_num] using (checked i).1

theorem core_radius (n : ℤ) :
    lowLinearRadius (Finset.Ico (-10241) (-9985)) n =
      blockLinearRadius (-10241) n radius := by
  apply (blockLinearRadius_eq_core KsIndex.PositiveEnergyAlphaLowProd.valid
    (-10241) n radius ?_ ?_).symm
  · intro i
    convert low_block_covered 6144 256 (by norm_num) i using 1; norm_num
  · intro i
    simpa only [radius, mode, show (-16385 : ℤ)+6144 = -10241 by norm_num] using (checked i).2
theorem core_m2 :
    lowLinearNumerator (Finset.Ico (-10241) (-9985)) (-2) = -59860457785631911894654268782914279370520727017 ∧
    lowLinearRadius (Finset.Ico (-10241) (-9985)) (-2) = 258633943782817850345005476882204128213 :=
  ⟨(core_center _).trans sum_m2.1, (core_radius _).trans sum_m2.2⟩
theorem core_m1 :
    lowLinearNumerator (Finset.Ico (-10241) (-9985)) (-1) = 59854537311640370343465125883898085909991751522 ∧
    lowLinearRadius (Finset.Ico (-10241) (-9985)) (-1) = 258608363388358612509647094385653143769 :=
  ⟨(core_center _).trans sum_m1.1, (core_radius _).trans sum_m1.2⟩
theorem core_p1 :
    lowLinearNumerator (Finset.Ico (-10241) (-9985)) (1) = 59842699876522287885049435830806378658604068613 ∧
    lowLinearRadius (Finset.Ico (-10241) (-9985)) (1) = 258557217777542918035618733757133424613 :=
  ⟨(core_center _).trans sum_p1.1, (core_radius _).trans sum_p1.2⟩
theorem core_p2 :
    lowLinearNumerator (Finset.Ico (-10241) (-9985)) (2) = -59836782914701001989355700575615447185669191616 ∧
    lowLinearRadius (Finset.Ico (-10241) (-9985)) (2) = 258531652558184627065528841345301401626 :=
  ⟨(core_center _).trans sum_p2.1, (core_radius _).trans sum_p2.2⟩
end KsIndex.AlphaRemarkTrial.Cache6144
