module

public import KsIndexLean.AlphaLowModeSumAssembly
public import KsIndexLean.AlphaLowBlockCertificate23808

@[expose] public section

namespace KsIndex.AlphaRemarkTrial.Cache23808
theorem core_center (n : ℤ) :
    lowLinearNumerator (Finset.Ico (7423) (7679)) n =
      blockLinearNumerator (7423) n center := by
  apply (blockLinearNumerator_eq_core KsIndex.PositiveEnergyAlphaLowProd.valid
    (7423) n center ?_ ?_).symm
  · intro i
    convert low_block_covered 23808 256 (by norm_num) i using 1; norm_num
  · intro i
    simpa only [center, mode, show (-16385 : ℤ)+23808 = 7423 by norm_num] using (checked i).1

theorem core_radius (n : ℤ) :
    lowLinearRadius (Finset.Ico (7423) (7679)) n =
      blockLinearRadius (7423) n radius := by
  apply (blockLinearRadius_eq_core KsIndex.PositiveEnergyAlphaLowProd.valid
    (7423) n radius ?_ ?_).symm
  · intro i
    convert low_block_covered 23808 256 (by norm_num) i using 1; norm_num
  · intro i
    simpa only [radius, mode, show (-16385 : ℤ)+23808 = 7423 by norm_num] using (checked i).2
theorem core_m2 :
    lowLinearNumerator (Finset.Ico (7423) (7679)) (-2) = 263606591638183716888632952119480489074870210392 ∧
    lowLinearRadius (Finset.Ico (7423) (7679)) (-2) = 404752316207656079823939193963116148508 :=
  ⟨(core_center _).trans sum_m2.1, (core_radius _).trans sum_m2.2⟩
theorem core_m1 :
    lowLinearNumerator (Finset.Ico (7423) (7679)) (-1) = -263641505455022717452915062965180710677504032001 ∧
    lowLinearRadius (Finset.Ico (7423) (7679)) (-1) = 404805924600188122335143837800587176698 :=
  ⟨(core_center _).trans sum_m1.1, (core_radius _).trans sum_m1.2⟩
theorem core_p1 :
    lowLinearNumerator (Finset.Ico (7423) (7679)) (1) = -263711360844025323333775817479315102019606849211 ∧
    lowLinearRadius (Finset.Ico (7423) (7679)) (1) = 404913184002376939936157387835466604605 :=
  ⟨(core_center _).trans sum_p1.1, (core_radius _).trans sum_p1.2⟩
theorem core_p2 :
    lowLinearNumerator (Finset.Ico (7423) (7679)) (2) = 263746302423545461789352432252144416341562404455 ∧
    lowLinearRadius (Finset.Ico (7423) (7679)) (2) = 404966835023329421778435736926764457072 :=
  ⟨(core_center _).trans sum_p2.1, (core_radius _).trans sum_p2.2⟩
end KsIndex.AlphaRemarkTrial.Cache23808
