module

public import KsIndexLean.AlphaLowModeSumAssembly
public import KsIndexLean.AlphaLowBlockCertificate28672

@[expose] public section

namespace KsIndex.AlphaRemarkTrial.Cache28672
theorem core_center (n : ℤ) :
    lowLinearNumerator (Finset.Ico (12287) (12543)) n =
      blockLinearNumerator (12287) n center := by
  apply (blockLinearNumerator_eq_core KsIndex.PositiveEnergyAlphaLowProd.valid
    (12287) n center ?_ ?_).symm
  · intro i
    convert low_block_covered 28672 256 (by norm_num) i using 1; norm_num
  · intro i
    simpa only [center, mode, show (-16385 : ℤ)+28672 = 12287 by norm_num] using (checked i).1

theorem core_radius (n : ℤ) :
    lowLinearRadius (Finset.Ico (12287) (12543)) n =
      blockLinearRadius (12287) n radius := by
  apply (blockLinearRadius_eq_core KsIndex.PositiveEnergyAlphaLowProd.valid
    (12287) n radius ?_ ?_).symm
  · intro i
    convert low_block_covered 28672 256 (by norm_num) i using 1; norm_num
  · intro i
    simpa only [radius, mode, show (-16385 : ℤ)+28672 = 12287 by norm_num] using (checked i).2
theorem core_m2 :
    lowLinearNumerator (Finset.Ico (12287) (12543)) (-2) = 126505305050192399505765376334950273302667670541 ∧
    lowLinearRadius (Finset.Ico (12287) (12543)) (-2) = 188780665346943743319861577342183772525 :=
  ⟨(core_center _).trans sum_m2.1, (core_radius _).trans sum_m2.2⟩
theorem core_m1 :
    lowLinearNumerator (Finset.Ico (12287) (12543)) (-1) = -126515494837598719032333582293806081280969770743 ∧
    lowLinearRadius (Finset.Ico (12287) (12543)) (-1) = 188795871339786548811702971825546188682 :=
  ⟨(core_center _).trans sum_m1.1, (core_radius _).trans sum_m1.2⟩
theorem core_p1 :
    lowLinearNumerator (Finset.Ico (12287) (12543)) (1) = -126535879337999765879680478601679714198274994674 ∧
    lowLinearRadius (Finset.Ico (12287) (12543)) (1) = 188826290675833027030650005708845019313 :=
  ⟨(core_center _).trans sum_p1.1, (core_radius _).trans sum_p1.2⟩
theorem core_p2 :
    lowLinearNumerator (Finset.Ico (12287) (12543)) (2) = 126546074051788236808554823879456760291374389907 ∧
    lowLinearRadius (Finset.Ico (12287) (12543)) (2) = 188841504020221190493288444829696205244 :=
  ⟨(core_center _).trans sum_p2.1, (core_radius _).trans sum_p2.2⟩
end KsIndex.AlphaRemarkTrial.Cache28672
