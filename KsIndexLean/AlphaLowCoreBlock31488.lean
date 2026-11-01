module

public import KsIndexLean.AlphaLowModeSumAssembly
public import KsIndexLean.AlphaLowBlockCertificate31488

@[expose] public section

namespace KsIndex.AlphaRemarkTrial.Cache31488
theorem core_center (n : ℤ) :
    lowLinearNumerator (Finset.Ico (15103) (15359)) n =
      blockLinearNumerator (15103) n center := by
  apply (blockLinearNumerator_eq_core KsIndex.PositiveEnergyAlphaLowProd.valid
    (15103) n center ?_ ?_).symm
  · intro i
    convert low_block_covered 31488 256 (by norm_num) i using 1; norm_num
  · intro i
    simpa only [center, mode, show (-16385 : ℤ)+31488 = 15103 by norm_num] using (checked i).1

theorem core_radius (n : ℤ) :
    lowLinearRadius (Finset.Ico (15103) (15359)) n =
      blockLinearRadius (15103) n radius := by
  apply (blockLinearRadius_eq_core KsIndex.PositiveEnergyAlphaLowProd.valid
    (15103) n radius ?_ ?_).symm
  · intro i
    convert low_block_covered 31488 256 (by norm_num) i using 1; norm_num
  · intro i
    simpa only [radius, mode, show (-16385 : ℤ)+31488 = 15103 by norm_num] using (checked i).2
theorem core_m2 :
    lowLinearNumerator (Finset.Ico (15103) (15359)) (-2) = 93572402904498628455572765362473748870616149075 ∧
    lowLinearRadius (Finset.Ico (15103) (15359)) (-2) = 138003407861497512154003076863064208010 :=
  ⟨(core_center _).trans sum_m2.1, (core_radius _).trans sum_m2.2⟩
theorem core_m1 :
    lowLinearNumerator (Finset.Ico (15103) (15359)) (-1) = -93578546408562660663234045354102776919364168702 ∧
    lowLinearRadius (Finset.Ico (15103) (15359)) (-1) = 138012468499243820302033867615107221246 :=
  ⟨(core_center _).trans sum_m1.1, (core_radius _).trans sum_m1.2⟩
theorem core_p1 :
    lowLinearNumerator (Finset.Ico (15103) (15359)) (1) = -93590835837179230257095835295624886686573023247 ∧
    lowLinearRadius (Finset.Ico (15103) (15359)) (1) = 138030593344555712899843455569196510121 :=
  ⟨(core_center _).trans sum_p1.1, (core_radius _).trans sum_p1.2⟩
theorem core_p2 :
    lowLinearNumerator (Finset.Ico (15103) (15359)) (2) = 93596981762049679986196401099679175979996843829 ∧
    lowLinearRadius (Finset.Ico (15103) (15359)) (2) = 138039657552590165987183361323402305198 :=
  ⟨(core_center _).trans sum_p2.1, (core_radius _).trans sum_p2.2⟩
end KsIndex.AlphaRemarkTrial.Cache31488
