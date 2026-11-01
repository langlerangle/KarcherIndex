module

public import KsIndexLean.AlphaLowModeSumAssembly
public import KsIndexLean.AlphaLowBlockCertificate22528

@[expose] public section

namespace KsIndex.AlphaRemarkTrial.Cache22528
theorem core_center (n : ℤ) :
    lowLinearNumerator (Finset.Ico (6143) (6399)) n =
      blockLinearNumerator (6143) n center := by
  apply (blockLinearNumerator_eq_core KsIndex.PositiveEnergyAlphaLowProd.valid
    (6143) n center ?_ ?_).symm
  · intro i
    convert low_block_covered 22528 256 (by norm_num) i using 1; norm_num
  · intro i
    simpa only [center, mode, show (-16385 : ℤ)+22528 = 6143 by norm_num] using (checked i).1

theorem core_radius (n : ℤ) :
    lowLinearRadius (Finset.Ico (6143) (6399)) n =
      blockLinearRadius (6143) n radius := by
  apply (blockLinearRadius_eq_core KsIndex.PositiveEnergyAlphaLowProd.valid
    (6143) n radius ?_ ?_).symm
  · intro i
    convert low_block_covered 22528 256 (by norm_num) i using 1; norm_num
  · intro i
    simpa only [radius, mode, show (-16385 : ℤ)+22528 = 6143 by norm_num] using (checked i).2
theorem core_m2 :
    lowLinearNumerator (Finset.Ico (6143) (6399)) (-2) = 346885653970675390659453757294773950760922652401 ∧
    lowLinearRadius (Finset.Ico (6143) (6399)) (-2) = 538306485011110400321777393837537210690 :=
  ⟨(core_center _).trans sum_m2.1, (core_radius _).trans sum_m2.2⟩
theorem core_m1 :
    lowLinearNumerator (Finset.Ico (6143) (6399)) (-1) = -346940980030258690632448135242235620388952997169 ∧
    lowLinearRadius (Finset.Ico (6143) (6399)) (-1) = 538392342158333087033209706758681031414 :=
  ⟨(core_center _).trans sum_m1.1, (core_radius _).trans sum_m1.2⟩
theorem core_p1 :
    lowLinearNumerator (Finset.Ico (6143) (6399)) (1) = -347051685118609456667242976444105273936135406652 ∧
    lowLinearRadius (Finset.Ico (6143) (6399)) (1) = 538564138653085458401214374922049895470 :=
  ⟨(core_center _).trans sum_p1.1, (core_radius _).trans sum_p1.2⟩
theorem core_p2 :
    lowLinearNumerator (Finset.Ico (6143) (6399)) (2) = 347107064164286206518461864883370054314806281182 ∧
    lowLinearRadius (Finset.Ico (6143) (6399)) (2) = 538650078026856048075854504782849380956 :=
  ⟨(core_center _).trans sum_p2.1, (core_radius _).trans sum_p2.2⟩
end KsIndex.AlphaRemarkTrial.Cache22528
