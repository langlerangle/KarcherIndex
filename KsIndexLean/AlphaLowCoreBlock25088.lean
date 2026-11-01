module

public import KsIndexLean.AlphaLowModeSumAssembly
public import KsIndexLean.AlphaLowBlockCertificate25088

@[expose] public section

namespace KsIndex.AlphaRemarkTrial.Cache25088
theorem core_center (n : ℤ) :
    lowLinearNumerator (Finset.Ico (8703) (8959)) n =
      blockLinearNumerator (8703) n center := by
  apply (blockLinearNumerator_eq_core KsIndex.PositiveEnergyAlphaLowProd.valid
    (8703) n center ?_ ?_).symm
  · intro i
    convert low_block_covered 25088 256 (by norm_num) i using 1; norm_num
  · intro i
    simpa only [center, mode, show (-16385 : ℤ)+25088 = 8703 by norm_num] using (checked i).1

theorem core_radius (n : ℤ) :
    lowLinearRadius (Finset.Ico (8703) (8959)) n =
      blockLinearRadius (8703) n radius := by
  apply (blockLinearRadius_eq_core KsIndex.PositiveEnergyAlphaLowProd.valid
    (8703) n radius ?_ ?_).symm
  · intro i
    convert low_block_covered 25088 256 (by norm_num) i using 1; norm_num
  · intro i
    simpa only [radius, mode, show (-16385 : ℤ)+25088 = 8703 by norm_num] using (checked i).2
theorem core_m2 :
    lowLinearNumerator (Finset.Ico (8703) (8959)) (-2) = 209167431696156581338025202496909437975905559422 ∧
    lowLinearRadius (Finset.Ico (8703) (8959)) (-2) = 318297611573896244463669543227090454371 :=
  ⟨(core_center _).trans sum_m2.1, (core_radius _).trans sum_m2.2⟩
theorem core_m1 :
    lowLinearNumerator (Finset.Ico (8703) (8959)) (-1) = -209191118710467249353900560304583822846808765030 ∧
    lowLinearRadius (Finset.Ico (8703) (8959)) (-1) = 318333657100987876410930232562617150299 :=
  ⟨(core_center _).trans sum_m1.1, (core_radius _).trans sum_m1.2⟩
theorem core_p1 :
    lowLinearNumerator (Finset.Ico (8703) (8959)) (1) = -209238508838374979307275814633658368136352874261 ∧
    lowLinearRadius (Finset.Ico (8703) (8959)) (1) = 318405772654231445916362027381213213679 :=
  ⟨(core_center _).trans sum_p1.1, (core_radius _).trans sum_p1.2⟩
theorem core_p2 :
    lowLinearNumerator (Finset.Ico (8703) (8959)) (2) = 209262211955620095568278981166389241477689982480 ∧
    lowLinearRadius (Finset.Ico (8703) (8959)) (2) = 318441842685934825893490956507033463909 :=
  ⟨(core_center _).trans sum_p2.1, (core_radius _).trans sum_p2.2⟩
end KsIndex.AlphaRemarkTrial.Cache25088
