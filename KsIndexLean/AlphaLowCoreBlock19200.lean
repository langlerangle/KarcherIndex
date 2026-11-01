module

public import KsIndexLean.AlphaLowModeSumAssembly
public import KsIndexLean.AlphaLowBlockCertificate19200

@[expose] public section

namespace KsIndex.AlphaRemarkTrial.Cache19200
theorem core_center (n : ℤ) :
    lowLinearNumerator (Finset.Ico (2815) (3071)) n =
      blockLinearNumerator (2815) n center := by
  apply (blockLinearNumerator_eq_core KsIndex.PositiveEnergyAlphaLowProd.valid
    (2815) n center ?_ ?_).symm
  · intro i
    convert low_block_covered 19200 256 (by norm_num) i using 1; norm_num
  · intro i
    simpa only [center, mode, show (-16385 : ℤ)+19200 = 2815 by norm_num] using (checked i).1

theorem core_radius (n : ℤ) :
    lowLinearRadius (Finset.Ico (2815) (3071)) n =
      blockLinearRadius (2815) n radius := by
  apply (blockLinearRadius_eq_core KsIndex.PositiveEnergyAlphaLowProd.valid
    (2815) n radius ?_ ?_).symm
  · intro i
    convert low_block_covered 19200 256 (by norm_num) i using 1; norm_num
  · intro i
    simpa only [radius, mode, show (-16385 : ℤ)+19200 = 2815 by norm_num] using (checked i).2
theorem core_m2 :
    lowLinearNumerator (Finset.Ico (2815) (3071)) (-2) = 1063213313342296411009630883720239566928878794370 ∧
    lowLinearRadius (Finset.Ico (2815) (3071)) (-2) = 1722393131854378458745209874491283623174 :=
  ⟨(core_center _).trans sum_m2.1, (core_radius _).trans sum_m2.2⟩
theorem core_m1 :
    lowLinearNumerator (Finset.Ico (2815) (3071)) (-1) = -1063575024817986268283675277876330151117015925083 ∧
    lowLinearRadius (Finset.Ico (2815) (3071)) (-1) = 1722979121065701541967340919426183277300 :=
  ⟨(core_center _).trans sum_m1.1, (core_radius _).trans sum_m1.2⟩
theorem core_p1 :
    lowLinearNumerator (Finset.Ico (2815) (3071)) (1) = -1064299187076923928301483220700285733194395156891 ∧
    lowLinearRadius (Finset.Ico (2815) (3071)) (1) = 1724152297243163085665262965992762370521 :=
  ⟨(core_center _).trans sum_p1.1, (core_radius _).trans sum_p1.2⟩
theorem core_p2 :
    lowLinearNumerator (Finset.Ico (2815) (3071)) (2) = 1064661638364355222714886060866111737838249615600 ∧
    lowLinearRadius (Finset.Ico (2815) (3071)) (2) = 1724739485026160029505404669758643360067 :=
  ⟨(core_center _).trans sum_p2.1, (core_radius _).trans sum_p2.2⟩
end KsIndex.AlphaRemarkTrial.Cache19200
