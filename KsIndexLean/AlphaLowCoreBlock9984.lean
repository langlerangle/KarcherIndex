module

public import KsIndexLean.AlphaLowModeSumAssembly
public import KsIndexLean.AlphaLowBlockCertificate9984

@[expose] public section

namespace KsIndex.AlphaRemarkTrial.Cache9984
theorem core_center (n : ℤ) :
    lowLinearNumerator (Finset.Ico (-6401) (-6145)) n =
      blockLinearNumerator (-6401) n center := by
  apply (blockLinearNumerator_eq_core KsIndex.PositiveEnergyAlphaLowProd.valid
    (-6401) n center ?_ ?_).symm
  · intro i
    convert low_block_covered 9984 256 (by norm_num) i using 1; norm_num
  · intro i
    simpa only [center, mode, show (-16385 : ℤ)+9984 = -6401 by norm_num] using (checked i).1

theorem core_radius (n : ℤ) :
    lowLinearRadius (Finset.Ico (-6401) (-6145)) n =
      blockLinearRadius (-6401) n radius := by
  apply (blockLinearRadius_eq_core KsIndex.PositiveEnergyAlphaLowProd.valid
    (-6401) n radius ?_ ?_).symm
  · intro i
    convert low_block_covered 9984 256 (by norm_num) i using 1; norm_num
  · intro i
    simpa only [radius, mode, show (-16385 : ℤ)+9984 = -6401 by norm_num] using (checked i).2
theorem core_m2 :
    lowLinearNumerator (Finset.Ico (-6401) (-6145)) (-2) = -111293098537576124310194503099877059812301714875 ∧
    lowLinearRadius (Finset.Ico (-6401) (-6145)) (-2) = 538357661210493453058891354743422774371 :=
  ⟨(core_center _).trans sum_m2.1, (core_radius _).trans sum_m2.2⟩
theorem core_m1 :
    lowLinearNumerator (Finset.Ico (-6401) (-6145)) (-1) = 111275348460700365713972698208856157473247441377 ∧
    lowLinearRadius (Finset.Ico (-6401) (-6145)) (-1) = 538271795899806458326937753056205370762 :=
  ⟨(core_center _).trans sum_m1.1, (core_radius _).trans sum_m1.2⟩
theorem core_p1 :
    lowLinearNumerator (Finset.Ico (-6401) (-6145)) (1) = 111239865289590514192751813097452191268869659860 ∧
    lowLinearRadius (Finset.Ico (-6401) (-6145)) (1) = 538100147434111364247510034705480961099 :=
  ⟨(core_center _).trans sum_p1.1, (core_radius _).trans sum_p1.2⟩
theorem core_p2 :
    lowLinearNumerator (Finset.Ico (-6401) (-6145)) (2) = -111222132189940404800447290732957980715067796502 ∧
    lowLinearRadius (Finset.Ico (-6401) (-6145)) (2) = 538014364252901705094409612510672847675 :=
  ⟨(core_center _).trans sum_p2.1, (core_radius _).trans sum_p2.2⟩
end KsIndex.AlphaRemarkTrial.Cache9984
