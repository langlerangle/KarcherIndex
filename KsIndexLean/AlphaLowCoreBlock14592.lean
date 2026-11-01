module

public import KsIndexLean.AlphaLowModeSumAssembly
public import KsIndexLean.AlphaLowBlockCertificate14592

@[expose] public section

namespace KsIndex.AlphaRemarkTrial.Cache14592
theorem core_center (n : ℤ) :
    lowLinearNumerator (Finset.Ico (-1793) (-1537)) n =
      blockLinearNumerator (-1793) n center := by
  apply (blockLinearNumerator_eq_core KsIndex.PositiveEnergyAlphaLowProd.valid
    (-1793) n center ?_ ?_).symm
  · intro i
    convert low_block_covered 14592 256 (by norm_num) i using 1; norm_num
  · intro i
    simpa only [center, mode, show (-16385 : ℤ)+14592 = -1793 by norm_num] using (checked i).1

theorem core_radius (n : ℤ) :
    lowLinearRadius (Finset.Ico (-1793) (-1537)) n =
      blockLinearRadius (-1793) n radius := by
  apply (blockLinearRadius_eq_core KsIndex.PositiveEnergyAlphaLowProd.valid
    (-1793) n radius ?_ ?_).symm
  · intro i
    convert low_block_covered 14592 256 (by norm_num) i using 1; norm_num
  · intro i
    simpa only [radius, mode, show (-16385 : ℤ)+14592 = -1793 by norm_num] using (checked i).2
theorem core_m2 :
    lowLinearNumerator (Finset.Ico (-1793) (-1537)) (-2) = -591112484084874968554657756520714118340001558463 ∧
    lowLinearRadius (Finset.Ico (-1793) (-1537)) (-2) = 4155779786746598494346991587466038663058 :=
  ⟨(core_center _).trans sum_m2.1, (core_radius _).trans sum_m2.2⟩
theorem core_m1 :
    lowLinearNumerator (Finset.Ico (-1793) (-1537)) (-1) = 590755687146621120171558415624460322611818769505 ∧
    lowLinearRadius (Finset.Ico (-1793) (-1537)) (-1) = 4153269741480685557852337175622987174840 :=
  ⟨(core_center _).trans sum_m1.1, (core_radius _).trans sum_m1.2⟩
theorem core_p1 :
    lowLinearNumerator (Finset.Ico (-1793) (-1537)) (1) = 590043386439963502781534610556871096946527833962 ∧
    lowLinearRadius (Finset.Ico (-1793) (-1537)) (1) = 4148258754123144283430043220657047248032 :=
  ⟨(core_center _).trans sum_p1.1, (core_radius _).trans sum_p1.2⟩
theorem core_p2 :
    lowLinearNumerator (Finset.Ico (-1793) (-1537)) (2) = -589687881107122346918172240383092366479402785553 ∧
    lowLinearRadius (Finset.Ico (-1793) (-1537)) (2) = 4145757801011793343216302820253484190360 :=
  ⟨(core_center _).trans sum_p2.1, (core_radius _).trans sum_p2.2⟩
end KsIndex.AlphaRemarkTrial.Cache14592
