module

public import KsIndexLean.AlphaLowModeSumAssembly
public import KsIndexLean.AlphaLowBlockCertificate1792

@[expose] public section

namespace KsIndex.AlphaRemarkTrial.Cache1792
theorem core_center (n : ℤ) :
    lowLinearNumerator (Finset.Ico (-14593) (-14337)) n =
      blockLinearNumerator (-14593) n center := by
  apply (blockLinearNumerator_eq_core KsIndex.PositiveEnergyAlphaLowProd.valid
    (-14593) n center ?_ ?_).symm
  · intro i
    convert low_block_covered 1792 256 (by norm_num) i using 1; norm_num
  · intro i
    simpa only [center, mode, show (-16385 : ℤ)+1792 = -14593 by norm_num] using (checked i).1

theorem core_radius (n : ℤ) :
    lowLinearRadius (Finset.Ico (-14593) (-14337)) n =
      blockLinearRadius (-14593) n radius := by
  apply (blockLinearRadius_eq_core KsIndex.PositiveEnergyAlphaLowProd.valid
    (-14593) n radius ?_ ?_).symm
  · intro i
    convert low_block_covered 1792 256 (by norm_num) i using 1; norm_num
  · intro i
    simpa only [radius, mode, show (-16385 : ℤ)+1792 = -14593 by norm_num] using (checked i).2
theorem core_m2 :
    lowLinearNumerator (Finset.Ico (-14593) (-14337)) (-2) = -37424166359605414032722351671401614424481530530 ∧
    lowLinearRadius (Finset.Ico (-14593) (-14337)) (-2) = 149396180853809811742460709211412484594 :=
  ⟨(core_center _).trans sum_m2.1, (core_radius _).trans sum_m2.2⟩
theorem core_m1 :
    lowLinearNumerator (Finset.Ico (-14593) (-14337)) (-1) = 37421578802182269916491750513400097334340718609 ∧
    lowLinearRadius (Finset.Ico (-14593) (-14337)) (-1) = 149385851342055489840671993841486821945 :=
  ⟨(core_center _).trans sum_m1.1, (core_radius _).trans sum_m1.2⟩
theorem core_p1 :
    lowLinearNumerator (Finset.Ico (-14593) (-14337)) (1) = 37416404760658871191533572584711881827673485412 ∧
    lowLinearRadius (Finset.Ico (-14593) (-14337)) (1) = 149365196603268613293413758150370769166 :=
  ⟨(core_center _).trans sum_p1.1, (core_radius _).trans sum_p1.2⟩
theorem core_p2 :
    lowLinearNumerator (Finset.Ico (-14593) (-14337)) (2) = -37413818276410217628814075732967227776307332515 ∧
    lowLinearRadius (Finset.Ico (-14593) (-14337)) (2) = 149354871375643644378176425095080820562 :=
  ⟨(core_center _).trans sum_p2.1, (core_radius _).trans sum_p2.2⟩
end KsIndex.AlphaRemarkTrial.Cache1792
