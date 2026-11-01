module

public import KsIndexLean.AlphaLowModeSumAssembly
public import KsIndexLean.AlphaLowBlockCertificate22272

@[expose] public section

namespace KsIndex.AlphaRemarkTrial.Cache22272
theorem core_center (n : ℤ) :
    lowLinearNumerator (Finset.Ico (5887) (6143)) n =
      blockLinearNumerator (5887) n center := by
  apply (blockLinearNumerator_eq_core KsIndex.PositiveEnergyAlphaLowProd.valid
    (5887) n center ?_ ?_).symm
  · intro i
    convert low_block_covered 22272 256 (by norm_num) i using 1; norm_num
  · intro i
    simpa only [center, mode, show (-16385 : ℤ)+22272 = 5887 by norm_num] using (checked i).1

theorem core_radius (n : ℤ) :
    lowLinearRadius (Finset.Ico (5887) (6143)) n =
      blockLinearRadius (5887) n radius := by
  apply (blockLinearRadius_eq_core KsIndex.PositiveEnergyAlphaLowProd.valid
    (5887) n radius ?_ ?_).symm
  · intro i
    convert low_block_covered 22272 256 (by norm_num) i using 1; norm_num
  · intro i
    simpa only [radius, mode, show (-16385 : ℤ)+22272 = 5887 by norm_num] using (checked i).2
theorem core_m2 :
    lowLinearNumerator (Finset.Ico (5887) (6143)) (-2) = 368935364005357229866723032893531067160778962911 ∧
    lowLinearRadius (Finset.Ico (5887) (6143)) (-2) = 573887413608483552536678909047881700584 :=
  ⟨(core_center _).trans sum_m2.1, (core_radius _).trans sum_m2.2⟩
theorem core_m1 :
    lowLinearNumerator (Finset.Ico (5887) (6143)) (-1) = -368996712641610473686231373649865402585749644855 ∧
    lowLinearRadius (Finset.Ico (5887) (6143)) (-1) = 573982843639595761950217849384892901847 :=
  ⟨(core_center _).trans sum_m1.1, (core_radius _).trans sum_m1.2⟩
theorem core_p1 :
    lowLinearNumerator (Finset.Ico (5887) (6143)) (1) = -369119471152093309059731255734367482198288562449 ∧
    lowLinearRadius (Finset.Ico (5887) (6143)) (1) = 574173798960535858242987666784243904102 :=
  ⟨(core_center _).trans sum_p1.1, (core_radius _).trans sum_p1.2⟩
theorem core_p2 :
    lowLinearNumerator (Finset.Ico (5887) (6143)) (2) = 369180881046705207316955887559862382684804045652 ∧
    lowLinearRadius (Finset.Ico (5887) (6143)) (2) = 574269324282069709052647323070138153236 :=
  ⟨(core_center _).trans sum_p2.1, (core_radius _).trans sum_p2.2⟩
end KsIndex.AlphaRemarkTrial.Cache22272
