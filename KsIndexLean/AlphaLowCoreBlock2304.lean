module

public import KsIndexLean.AlphaLowModeSumAssembly
public import KsIndexLean.AlphaLowBlockCertificate2304

@[expose] public section

namespace KsIndex.AlphaRemarkTrial.Cache2304
theorem core_center (n : ℤ) :
    lowLinearNumerator (Finset.Ico (-14081) (-13825)) n =
      blockLinearNumerator (-14081) n center := by
  apply (blockLinearNumerator_eq_core KsIndex.PositiveEnergyAlphaLowProd.valid
    (-14081) n center ?_ ?_).symm
  · intro i
    convert low_block_covered 2304 256 (by norm_num) i using 1; norm_num
  · intro i
    simpa only [center, mode, show (-16385 : ℤ)+2304 = -14081 by norm_num] using (checked i).1

theorem core_radius (n : ℤ) :
    lowLinearRadius (Finset.Ico (-14081) (-13825)) n =
      blockLinearRadius (-14081) n radius := by
  apply (blockLinearRadius_eq_core KsIndex.PositiveEnergyAlphaLowProd.valid
    (-14081) n radius ?_ ?_).symm
  · intro i
    convert low_block_covered 2304 256 (by norm_num) i using 1; norm_num
  · intro i
    simpa only [radius, mode, show (-16385 : ℤ)+2304 = -14081 by norm_num] using (checked i).2
theorem core_m2 :
    lowLinearNumerator (Finset.Ico (-14081) (-13825)) (-2) = -39243392756504229931776503445824445035208211187 ∧
    lowLinearRadius (Finset.Ico (-14081) (-13825)) (-2) = 157880442254457452259327843913785755707 :=
  ⟨(core_center _).trans sum_m2.1, (core_radius _).trans sum_m2.2⟩
theorem core_m1 :
    lowLinearNumerator (Finset.Ico (-14081) (-13825)) (-1) = 39240579830518457507187383784281166983690616575 ∧
    lowLinearRadius (Finset.Ico (-14081) (-13825)) (-1) = 157869125478287350114049137980881617559 :=
  ⟨(core_center _).trans sum_m1.1, (core_radius _).trans sum_m1.2⟩
theorem core_p1 :
    lowLinearNumerator (Finset.Ico (-14081) (-13825)) (1) = 39234955188173265303387606985813623264594920693 ∧
    lowLinearRadius (Finset.Ico (-14081) (-13825)) (1) = 157846496792464698847318953507694353580 :=
  ⟨(core_center _).trans sum_p1.1, (core_radius _).trans sum_p1.2⟩
theorem core_p2 :
    lowLinearNumerator (Finset.Ico (-14081) (-13825)) (2) = -39232143471640463538195545844007454821052338008 ∧
    lowLinearRadius (Finset.Ico (-14081) (-13825)) (2) = 157835184882114602428176713038248806653 :=
  ⟨(core_center _).trans sum_p2.1, (core_radius _).trans sum_p2.2⟩
end KsIndex.AlphaRemarkTrial.Cache2304
