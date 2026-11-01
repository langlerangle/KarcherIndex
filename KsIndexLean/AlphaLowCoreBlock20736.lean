module

public import KsIndexLean.AlphaLowModeSumAssembly
public import KsIndexLean.AlphaLowBlockCertificate20736

@[expose] public section

namespace KsIndex.AlphaRemarkTrial.Cache20736
theorem core_center (n : ℤ) :
    lowLinearNumerator (Finset.Ico (4351) (4607)) n =
      blockLinearNumerator (4351) n center := by
  apply (blockLinearNumerator_eq_core KsIndex.PositiveEnergyAlphaLowProd.valid
    (4351) n center ?_ ?_).symm
  · intro i
    convert low_block_covered 20736 256 (by norm_num) i using 1; norm_num
  · intro i
    simpa only [center, mode, show (-16385 : ℤ)+20736 = 4351 by norm_num] using (checked i).1

theorem core_radius (n : ℤ) :
    lowLinearRadius (Finset.Ico (4351) (4607)) n =
      blockLinearRadius (4351) n radius := by
  apply (blockLinearRadius_eq_core KsIndex.PositiveEnergyAlphaLowProd.valid
    (4351) n radius ?_ ?_).symm
  · intro i
    convert low_block_covered 20736 256 (by norm_num) i using 1; norm_num
  · intro i
    simpa only [radius, mode, show (-16385 : ℤ)+20736 = 4351 by norm_num] using (checked i).2
theorem core_m2 :
    lowLinearNumerator (Finset.Ico (4351) (4607)) (-2) = 570687015717114370526345654310702611433253982727 ∧
    lowLinearRadius (Finset.Ico (4351) (4607)) (-2) = 902751615483345667860880502341976107549 :=
  ⟨(core_center _).trans sum_m2.1, (core_radius _).trans sum_m2.2⟩
theorem core_m1 :
    lowLinearNumerator (Finset.Ico (4351) (4607)) (-1) = -570814487224945417541886792837267335600710648840 ∧
    lowLinearRadius (Finset.Ico (4351) (4607)) (-1) = 902953261719913524758324322855360069940 :=
  ⟨(core_center _).trans sum_m1.1, (core_radius _).trans sum_m1.2⟩
theorem core_p1 :
    lowLinearNumerator (Finset.Ico (4351) (4607)) (1) = -571069601199564157689547671240664492882041567364 ∧
    lowLinearRadius (Finset.Ico (4351) (4607)) (1) = 903356824635941306562777907340995272582 :=
  ⟨(core_center _).trans sum_p1.1, (core_radius _).trans sum_p1.2⟩
theorem core_p2 :
    lowLinearNumerator (Finset.Ico (4351) (4607)) (2) = 571197243742817204390297096256736505460736588063 ∧
    lowLinearRadius (Finset.Ico (4351) (4607)) (2) = 903558741436364948841980015897223108842 :=
  ⟨(core_center _).trans sum_p2.1, (core_radius _).trans sum_p2.2⟩
end KsIndex.AlphaRemarkTrial.Cache20736
