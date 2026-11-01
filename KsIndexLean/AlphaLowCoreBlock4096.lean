module

public import KsIndexLean.AlphaLowModeSumAssembly
public import KsIndexLean.AlphaLowBlockCertificate4096

@[expose] public section

namespace KsIndex.AlphaRemarkTrial.Cache4096
theorem core_center (n : ℤ) :
    lowLinearNumerator (Finset.Ico (-12289) (-12033)) n =
      blockLinearNumerator (-12289) n center := by
  apply (blockLinearNumerator_eq_core KsIndex.PositiveEnergyAlphaLowProd.valid
    (-12289) n center ?_ ?_).symm
  · intro i
    convert low_block_covered 4096 256 (by norm_num) i using 1; norm_num
  · intro i
    simpa only [center, mode, show (-16385 : ℤ)+4096 = -12289 by norm_num] using (checked i).1

theorem core_radius (n : ℤ) :
    lowLinearRadius (Finset.Ico (-12289) (-12033)) n =
      blockLinearRadius (-12289) n radius := by
  apply (blockLinearRadius_eq_core KsIndex.PositiveEnergyAlphaLowProd.valid
    (-12289) n radius ?_ ?_).symm
  · intro i
    convert low_block_covered 4096 256 (by norm_num) i using 1; norm_num
  · intro i
    simpa only [radius, mode, show (-16385 : ℤ)+4096 = -12289 by norm_num] using (checked i).2
theorem core_m2 :
    lowLinearNumerator (Finset.Ico (-12289) (-12033)) (-2) = -47016101802557665446626674183581378651514629499 ∧
    lowLinearRadius (Finset.Ico (-12289) (-12033)) (-2) = 194917584184188253331991964876543278070 :=
  ⟨(core_center _).trans sum_m2.1, (core_radius _).trans sum_m2.2⟩
theorem core_m1 :
    lowLinearNumerator (Finset.Ico (-12289) (-12033)) (-1) = 47012235016573406063107503885277538595762659803 ∧
    lowLinearRadius (Finset.Ico (-12289) (-12033)) (-1) = 194901553277777836627628551664307639522 :=
  ⟨(core_center _).trans sum_m1.1, (core_radius _).trans sum_m1.2⟩
theorem core_p1 :
    lowLinearNumerator (Finset.Ico (-12289) (-12033)) (1) = 47004503352478093921550680223642346895602269474 ∧
    lowLinearRadius (Finset.Ico (-12289) (-12033)) (1) = 194869499374674855327619661472271744181 :=
  ⟨(core_center _).trans sum_p1.1, (core_radius _).trans sum_p1.2⟩
theorem core_p2 :
    lowLinearNumerator (Finset.Ico (-12289) (-12033)) (2) = -47000638474053273671055183594696291259492158729 ∧
    lowLinearRadius (Finset.Ico (-12289) (-12033)) (2) = 194853476376681453467490223201707375366 :=
  ⟨(core_center _).trans sum_p2.1, (core_radius _).trans sum_p2.2⟩
end KsIndex.AlphaRemarkTrial.Cache4096
