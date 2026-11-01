module

public import KsIndexLean.AlphaLowModeSumAssembly
public import KsIndexLean.AlphaLowBlockCertificate26624

@[expose] public section

namespace KsIndex.AlphaRemarkTrial.Cache26624
theorem core_center (n : ℤ) :
    lowLinearNumerator (Finset.Ico (10239) (10495)) n =
      blockLinearNumerator (10239) n center := by
  apply (blockLinearNumerator_eq_core KsIndex.PositiveEnergyAlphaLowProd.valid
    (10239) n center ?_ ?_).symm
  · intro i
    convert low_block_covered 26624 256 (by norm_num) i using 1; norm_num
  · intro i
    simpa only [center, mode, show (-16385 : ℤ)+26624 = 10239 by norm_num] using (checked i).1

theorem core_radius (n : ℤ) :
    lowLinearRadius (Finset.Ico (10239) (10495)) n =
      blockLinearRadius (10239) n radius := by
  apply (blockLinearRadius_eq_core KsIndex.PositiveEnergyAlphaLowProd.valid
    (10239) n radius ?_ ?_).symm
  · intro i
    convert low_block_covered 26624 256 (by norm_num) i using 1; norm_num
  · intro i
    simpa only [radius, mode, show (-16385 : ℤ)+26624 = 10239 by norm_num] using (checked i).2
theorem core_m2 :
    lowLinearNumerator (Finset.Ico (10239) (10495)) (-2) = 165066926697412473310473752361232707966861185628 ∧
    lowLinearRadius (Finset.Ico (10239) (10495)) (-2) = 248888922532233476699062832495664310883 :=
  ⟨(core_center _).trans sum_m2.1, (core_radius _).trans sum_m2.2⟩
theorem core_m1 :
    lowLinearNumerator (Finset.Ico (10239) (10495)) (-1) = -165082849507546036284034073149670689004926209476 ∧
    lowLinearRadius (Finset.Ico (10239) (10495)) (-1) = 248912931112822198781295565551639478827 :=
  ⟨(core_center _).trans sum_m1.1, (core_radius _).trans sum_m1.2⟩
theorem core_p1 :
    lowLinearNumerator (Finset.Ico (10239) (10495)) (1) = -165114704345808536659930062863975725959835095602 ∧
    lowLinearRadius (Finset.Ico (10239) (10495)) (1) = 248960962173030546622551656250731484854 :=
  ⟨(core_center _).trans sum_p1.1, (core_radius _).trans sum_p1.2⟩
theorem core_p2 :
    lowLinearNumerator (Finset.Ico (10239) (10495)) (2) = 165130636375716556124307435508319997738639362633 ∧
    lowLinearRadius (Finset.Ico (10239) (10495)) (2) = 248984984655332706669493995404533721504 :=
  ⟨(core_center _).trans sum_p2.1, (core_radius _).trans sum_p2.2⟩
end KsIndex.AlphaRemarkTrial.Cache26624
