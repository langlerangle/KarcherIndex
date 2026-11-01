module

public import KsIndexLean.AlphaLowModeSumAssembly
public import KsIndexLean.AlphaLowBlockCertificate1536

@[expose] public section

namespace KsIndex.AlphaRemarkTrial.Cache1536
theorem core_center (n : ℤ) :
    lowLinearNumerator (Finset.Ico (-14849) (-14593)) n =
      blockLinearNumerator (-14849) n center := by
  apply (blockLinearNumerator_eq_core KsIndex.PositiveEnergyAlphaLowProd.valid
    (-14849) n center ?_ ?_).symm
  · intro i
    convert low_block_covered 1536 256 (by norm_num) i using 1; norm_num
  · intro i
    simpa only [center, mode, show (-16385 : ℤ)+1536 = -14849 by norm_num] using (checked i).1

theorem core_radius (n : ℤ) :
    lowLinearRadius (Finset.Ico (-14849) (-14593)) n =
      blockLinearRadius (-14849) n radius := by
  apply (blockLinearRadius_eq_core KsIndex.PositiveEnergyAlphaLowProd.valid
    (-14849) n radius ?_ ?_).symm
  · intro i
    convert low_block_covered 1536 256 (by norm_num) i using 1; norm_num
  · intro i
    simpa only [radius, mode, show (-16385 : ℤ)+1536 = -14849 by norm_num] using (checked i).2
theorem core_m2 :
    lowLinearNumerator (Finset.Ico (-14849) (-14593)) (-2) = -36568837685671984246974240439468906317998928213 ∧
    lowLinearRadius (Finset.Ico (-14849) (-14593)) (-2) = 145432827540593161953312239300807980016 :=
  ⟨(core_center _).trans sum_m2.1, (core_radius _).trans sum_m2.2⟩
theorem core_m1 :
    lowLinearNumerator (Finset.Ico (-14849) (-14593)) (-1) = 36566353244481930552877974980896976808475866194 ∧
    lowLinearRadius (Finset.Ico (-14849) (-14593)) (-1) = 145422946962407992338284741890096758265 :=
  ⟨(core_center _).trans sum_m1.1, (core_radius _).trans sum_m1.2⟩
theorem core_p1 :
    lowLinearNumerator (Finset.Ico (-14849) (-14593)) (1) = 36561385374728750782935537830510842522668378706 ∧
    lowLinearRadius (Finset.Ico (-14849) (-14593)) (1) = 145403189833258597400324442459230489766 :=
  ⟨(core_center _).trans sum_p1.1, (core_radius _).trans sum_p1.2⟩
theorem core_p2 :
    lowLinearNumerator (Finset.Ico (-14849) (-14593)) (2) = -36558901946028052593906928787191408675518869375 ∧
    lowLinearRadius (Finset.Ico (-14849) (-14593)) (2) = 145393313281747244330937410594538883680 :=
  ⟨(core_center _).trans sum_p2.1, (core_radius _).trans sum_p2.2⟩
end KsIndex.AlphaRemarkTrial.Cache1536
