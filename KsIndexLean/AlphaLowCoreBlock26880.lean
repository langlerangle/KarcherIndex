module

public import KsIndexLean.AlphaLowModeSumAssembly
public import KsIndexLean.AlphaLowBlockCertificate26880

@[expose] public section

namespace KsIndex.AlphaRemarkTrial.Cache26880
theorem core_center (n : ℤ) :
    lowLinearNumerator (Finset.Ico (10495) (10751)) n =
      blockLinearNumerator (10495) n center := by
  apply (blockLinearNumerator_eq_core KsIndex.PositiveEnergyAlphaLowProd.valid
    (10495) n center ?_ ?_).symm
  · intro i
    convert low_block_covered 26880 256 (by norm_num) i using 1; norm_num
  · intro i
    simpa only [center, mode, show (-16385 : ℤ)+26880 = 10495 by norm_num] using (checked i).1

theorem core_radius (n : ℤ) :
    lowLinearRadius (Finset.Ico (10495) (10751)) n =
      blockLinearRadius (10495) n radius := by
  apply (blockLinearRadius_eq_core KsIndex.PositiveEnergyAlphaLowProd.valid
    (10495) n radius ?_ ?_).symm
  · intro i
    convert low_block_covered 26880 256 (by norm_num) i using 1; norm_num
  · intro i
    simpa only [radius, mode, show (-16385 : ℤ)+26880 = 10495 by norm_num] using (checked i).2
theorem core_m2 :
    lowLinearNumerator (Finset.Ico (10495) (10751)) (-2) = 159228625833406787303606766161437826332759274600 ∧
    lowLinearRadius (Finset.Ico (10495) (10751)) (-2) = 239749987350973042840246846876207330514 :=
  ⟨(core_center _).trans sum_m2.1, (core_radius _).trans sum_m2.2⟩
theorem core_m1 :
    lowLinearNumerator (Finset.Ico (10495) (10751)) (-1) = -159243615263497156693015484150795028050001865888 ∧
    lowLinearRadius (Finset.Ico (10495) (10751)) (-1) = 239772556946337733353350614465512859349 :=
  ⟨(core_center _).trans sum_m1.1, (core_radius _).trans sum_m1.2⟩
theorem core_p1 :
    lowLinearNumerator (Finset.Ico (10495) (10751)) (1) = -159273602592112576074040328691655390427590041429 ∧
    lowLinearRadius (Finset.Ico (10495) (10751)) (1) = 239817708888030549636950170301996076358 :=
  ⟨(core_center _).trans sum_p1.1, (core_radius _).trans sum_p1.2⟩
theorem core_p2 :
    lowLinearNumerator (Finset.Ico (10495) (10751)) (2) = 159288600492232630251711367909696490482519810763 ∧
    lowLinearRadius (Finset.Ico (10495) (10751)) (2) = 239840291236760287666431447431921507009 :=
  ⟨(core_center _).trans sum_p2.1, (core_radius _).trans sum_p2.2⟩
end KsIndex.AlphaRemarkTrial.Cache26880
