module

public import KsIndexLean.AlphaLowModeSumAssembly
public import KsIndexLean.AlphaLowBlockCertificate19968

@[expose] public section

namespace KsIndex.AlphaRemarkTrial.Cache19968
theorem core_center (n : ℤ) :
    lowLinearNumerator (Finset.Ico (3583) (3839)) n =
      blockLinearNumerator (3583) n center := by
  apply (blockLinearNumerator_eq_core KsIndex.PositiveEnergyAlphaLowProd.valid
    (3583) n center ?_ ?_).symm
  · intro i
    convert low_block_covered 19968 256 (by norm_num) i using 1; norm_num
  · intro i
    simpa only [center, mode, show (-16385 : ℤ)+19968 = 3583 by norm_num] using (checked i).1

theorem core_radius (n : ℤ) :
    lowLinearRadius (Finset.Ico (3583) (3839)) n =
      blockLinearRadius (3583) n radius := by
  apply (blockLinearRadius_eq_core KsIndex.PositiveEnergyAlphaLowProd.valid
    (3583) n radius ?_ ?_).symm
  · intro i
    convert low_block_covered 19968 256 (by norm_num) i using 1; norm_num
  · intro i
    simpa only [radius, mode, show (-16385 : ℤ)+19968 = 3583 by norm_num] using (checked i).2
theorem core_m2 :
    lowLinearNumerator (Finset.Ico (3583) (3839)) (-2) = 753986065056188883438372667322074745211831151055 ∧
    lowLinearRadius (Finset.Ico (3583) (3839)) (-2) = 1205514313081652344624434209043394988862 :=
  ⟨(core_center _).trans sum_m2.1, (core_radius _).trans sum_m2.2⟩
theorem core_m1 :
    lowLinearNumerator (Finset.Ico (3583) (3839)) (-1) = -754189386208710199087917534901014335038924297864 ∧
    lowLinearRadius (Finset.Ico (3583) (3839)) (-1) = 1205839401404115661006433355833564253746 :=
  ⟨(core_center _).trans sum_m1.1, (core_radius _).trans sum_m1.2⟩
theorem core_p1 :
    lowLinearNumerator (Finset.Ico (3583) (3839)) (1) = -754596357789468508760605179677637440521719920398 ∧
    lowLinearRadius (Finset.Ico (3583) (3839)) (1) = 1206490104536781853976591802307261338265 :=
  ⟨(core_center _).trans sum_p1.1, (core_radius _).trans sum_p1.2⟩
theorem core_p2 :
    lowLinearNumerator (Finset.Ico (3583) (3839)) (2) = 754800008395576489116896092993846529271329704972 ∧
    lowLinearRadius (Finset.Ico (3583) (3839)) (2) = 1206815719631393784186024375336731476265 :=
  ⟨(core_center _).trans sum_p2.1, (core_radius _).trans sum_p2.2⟩
end KsIndex.AlphaRemarkTrial.Cache19968
