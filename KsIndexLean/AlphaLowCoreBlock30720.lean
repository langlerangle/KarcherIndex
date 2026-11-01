module

public import KsIndexLean.AlphaLowModeSumAssembly
public import KsIndexLean.AlphaLowBlockCertificate30720

@[expose] public section

namespace KsIndex.AlphaRemarkTrial.Cache30720
theorem core_center (n : ℤ) :
    lowLinearNumerator (Finset.Ico (14335) (14591)) n =
      blockLinearNumerator (14335) n center := by
  apply (blockLinearNumerator_eq_core KsIndex.PositiveEnergyAlphaLowProd.valid
    (14335) n center ?_ ?_).symm
  · intro i
    convert low_block_covered 30720 256 (by norm_num) i using 1; norm_num
  · intro i
    simpa only [center, mode, show (-16385 : ℤ)+30720 = 14335 by norm_num] using (checked i).1

theorem core_radius (n : ℤ) :
    lowLinearRadius (Finset.Ico (14335) (14591)) n =
      blockLinearRadius (14335) n radius := by
  apply (blockLinearRadius_eq_core KsIndex.PositiveEnergyAlphaLowProd.valid
    (14335) n radius ?_ ?_).symm
  · intro i
    convert low_block_covered 30720 256 (by norm_num) i using 1; norm_num
  · intro i
    simpa only [radius, mode, show (-16385 : ℤ)+30720 = 14335 by norm_num] using (checked i).2
theorem core_m2 :
    lowLinearNumerator (Finset.Ico (14335) (14591)) (-2) = 100991824515860196237755258415916116550189896251 ∧
    lowLinearRadius (Finset.Ico (14335) (14591)) (-2) = 149389965093287633951753223575206996663 :=
  ⟨(core_center _).trans sum_m2.1, (core_radius _).trans sum_m2.2⟩
theorem core_m1 :
    lowLinearNumerator (Finset.Ico (14335) (14591)) (-1) = -100998807255742682592475024479945682147507099417 ∧
    lowLinearRadius (Finset.Ico (14335) (14591)) (-1) = 149400294175262376091023478567177715545 :=
  ⟨(core_center _).trans sum_m1.1, (core_radius _).trans sum_m1.2⟩
theorem core_p1 :
    lowLinearNumerator (Finset.Ico (14335) (14591)) (1) = -101012775632772260058763457004425144714373189686 ∧
    lowLinearRadius (Finset.Ico (14335) (14591)) (1) = 149420956624940537698498766098278334587 :=
  ⟨(core_center _).trans sum_p1.1, (core_radius _).trans sum_p1.2⟩
theorem core_p2 :
    lowLinearNumerator (Finset.Ico (14335) (14591)) (2) = 101019761270320098445048346526462099345604899532 ∧
    lowLinearRadius (Finset.Ico (14335) (14591)) (2) = 149431289993236756548861592840313797459 :=
  ⟨(core_center _).trans sum_p2.1, (core_radius _).trans sum_p2.2⟩
end KsIndex.AlphaRemarkTrial.Cache30720
