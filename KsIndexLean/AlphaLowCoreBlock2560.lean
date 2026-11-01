module

public import KsIndexLean.AlphaLowModeSumAssembly
public import KsIndexLean.AlphaLowBlockCertificate2560

@[expose] public section

namespace KsIndex.AlphaRemarkTrial.Cache2560
theorem core_center (n : ℤ) :
    lowLinearNumerator (Finset.Ico (-13825) (-13569)) n =
      blockLinearNumerator (-13825) n center := by
  apply (blockLinearNumerator_eq_core KsIndex.PositiveEnergyAlphaLowProd.valid
    (-13825) n center ?_ ?_).symm
  · intro i
    convert low_block_covered 2560 256 (by norm_num) i using 1; norm_num
  · intro i
    simpa only [center, mode, show (-16385 : ℤ)+2560 = -13825 by norm_num] using (checked i).1

theorem core_radius (n : ℤ) :
    lowLinearRadius (Finset.Ico (-13825) (-13569)) n =
      blockLinearRadius (-13825) n radius := by
  apply (blockLinearRadius_eq_core KsIndex.PositiveEnergyAlphaLowProd.valid
    (-13825) n radius ?_ ?_).symm
  · intro i
    convert low_block_covered 2560 256 (by norm_num) i using 1; norm_num
  · intro i
    simpa only [radius, mode, show (-16385 : ℤ)+2560 = -13825 by norm_num] using (checked i).2
theorem core_m2 :
    lowLinearNumerator (Finset.Ico (-13825) (-13569)) (-2) = -40211741887345958973528590237981098812934493187 ∧
    lowLinearRadius (Finset.Ico (-13825) (-13569)) (-2) = 162426083828218607694123369964247915402 :=
  ⟨(core_center _).trans sum_m2.1, (core_radius _).trans sum_m2.2⟩
theorem core_m1 :
    lowLinearNumerator (Finset.Ico (-13825) (-13569)) (-1) = 40208805668492882450577846057884207827563765707 ∧
    lowLinearRadius (Finset.Ico (-13825) (-13569)) (-1) = 162414223572555682321729445199337049381 :=
  ⟨(core_center _).trans sum_m1.1, (core_radius _).trans sum_m1.2⟩
theorem core_p1 :
    lowLinearNumerator (Finset.Ico (-13825) (-13569)) (1) = 40202934517033898291596656664481830260355696404 ∧
    lowLinearRadius (Finset.Ico (-13825) (-13569)) (1) = 162390508256795043229930363523507945316 :=
  ⟨(core_center _).trans sum_p1.1, (core_radius _).trans sum_p1.2⟩
theorem core_p2 :
    lowLinearNumerator (Finset.Ico (-13825) (-13569)) (2) = -40199999584240180048116632653420294719092604667 ∧
    lowLinearRadius (Finset.Ico (-13825) (-13569)) (2) = 162378653195938697392121976509535729334 :=
  ⟨(core_center _).trans sum_p2.1, (core_radius _).trans sum_p2.2⟩
end KsIndex.AlphaRemarkTrial.Cache2560
