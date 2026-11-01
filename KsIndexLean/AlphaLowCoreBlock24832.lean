module

public import KsIndexLean.AlphaLowModeSumAssembly
public import KsIndexLean.AlphaLowBlockCertificate24832

@[expose] public section

namespace KsIndex.AlphaRemarkTrial.Cache24832
theorem core_center (n : ℤ) :
    lowLinearNumerator (Finset.Ico (8447) (8703)) n =
      blockLinearNumerator (8447) n center := by
  apply (blockLinearNumerator_eq_core KsIndex.PositiveEnergyAlphaLowProd.valid
    (8447) n center ?_ ?_).symm
  · intro i
    convert low_block_covered 24832 256 (by norm_num) i using 1; norm_num
  · intro i
    simpa only [center, mode, show (-16385 : ℤ)+24832 = 8447 by norm_num] using (checked i).1

theorem core_radius (n : ℤ) :
    lowLinearRadius (Finset.Ico (8447) (8703)) n =
      blockLinearRadius (8447) n radius := by
  apply (blockLinearRadius_eq_core KsIndex.PositiveEnergyAlphaLowProd.valid
    (8447) n radius ?_ ?_).symm
  · intro i
    convert low_block_covered 24832 256 (by norm_num) i using 1; norm_num
  · intro i
    simpa only [radius, mode, show (-16385 : ℤ)+24832 = 8447 by norm_num] using (checked i).2
theorem core_m2 :
    lowLinearNumerator (Finset.Ico (8447) (8703)) (-2) = 218455868320098376747470419843350564532454709517 ∧
    lowLinearRadius (Finset.Ico (8447) (8703)) (-2) = 332992925441007210259603261219773210771 :=
  ⟨(core_center _).trans sum_m2.1, (core_radius _).trans sum_m2.2⟩
theorem core_m1 :
    lowLinearNumerator (Finset.Ico (8447) (8703)) (-1) = -218481345938597468366928892747876621246601491163 ∧
    lowLinearRadius (Finset.Ico (8447) (8703)) (-1) = 333031761215333708095776631032683916206 :=
  ⟨(core_center _).trans sum_m1.1, (core_radius _).trans sum_m1.2⟩
theorem core_p1 :
    lowLinearNumerator (Finset.Ico (8447) (8703)) (1) = -218532319009185405572803718861747566634930163147 ∧
    lowLinearRadius (Finset.Ico (8447) (8703)) (1) = 333109459948011507433518567595796885006 :=
  ⟨(core_center _).trans sum_p1.1, (core_radius _).trans sum_p1.2⟩
theorem core_p2 :
    lowLinearNumerator (Finset.Ico (8447) (8703)) (2) = 218557814465436043378503778542063584100111252205 ∧
    lowLinearRadius (Finset.Ico (8447) (8703)) (2) = 333148322912706722060621864007989702589 :=
  ⟨(core_center _).trans sum_p2.1, (core_radius _).trans sum_p2.2⟩
end KsIndex.AlphaRemarkTrial.Cache24832
