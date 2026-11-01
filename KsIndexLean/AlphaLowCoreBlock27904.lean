module

public import KsIndexLean.AlphaLowModeSumAssembly
public import KsIndexLean.AlphaLowBlockCertificate27904

@[expose] public section

namespace KsIndex.AlphaRemarkTrial.Cache27904
theorem core_center (n : ℤ) :
    lowLinearNumerator (Finset.Ico (11519) (11775)) n =
      blockLinearNumerator (11519) n center := by
  apply (blockLinearNumerator_eq_core KsIndex.PositiveEnergyAlphaLowProd.valid
    (11519) n center ?_ ?_).symm
  · intro i
    convert low_block_covered 27904 256 (by norm_num) i using 1; norm_num
  · intro i
    simpa only [center, mode, show (-16385 : ℤ)+27904 = 11519 by norm_num] using (checked i).1

theorem core_radius (n : ℤ) :
    lowLinearRadius (Finset.Ico (11519) (11775)) n =
      blockLinearRadius (11519) n radius := by
  apply (blockLinearRadius_eq_core KsIndex.PositiveEnergyAlphaLowProd.valid
    (11519) n radius ?_ ?_).symm
  · intro i
    convert low_block_covered 27904 256 (by norm_num) i using 1; norm_num
  · intro i
    simpa only [radius, mode, show (-16385 : ℤ)+27904 = 11519 by norm_num] using (checked i).2
theorem core_m2 :
    lowLinearNumerator (Finset.Ico (11519) (11775)) (-2) = 139005479581894402237237030739470835610965377554 ∧
    lowLinearRadius (Finset.Ico (11519) (11775)) (-2) = 208196906130428356679558483198147774600 :=
  ⟨(core_center _).trans sum_m2.1, (core_radius _).trans sum_m2.2⟩
theorem core_m1 :
    lowLinearNumerator (Finset.Ico (11519) (11775)) (-1) = -139017414620838192287319192848694113646108303734 ∧
    lowLinearRadius (Finset.Ico (11519) (11775)) (-1) = 208214782000760105217696854741272968386 :=
  ⟨(core_center _).trans sum_m1.1, (core_radius _).trans sum_m1.2⟩
theorem core_p1 :
    lowLinearNumerator (Finset.Ico (11519) (11775)) (1) = -139041290848498726420747881125494905124736265598 ∧
    lowLinearRadius (Finset.Ico (11519) (11775)) (1) = 208250542952352752937983349814533361961 :=
  ⟨(core_center _).trans sum_p1.1, (core_radius _).trans sum_p1.2⟩
theorem core_p2 :
    lowLinearNumerator (Finset.Ico (11519) (11775)) (2) = 139053232038271869199902727386325381904377312336 ∧
    lowLinearRadius (Finset.Ico (11519) (11775)) (2) = 208268428035195895255936714370921543360 :=
  ⟨(core_center _).trans sum_p2.1, (core_radius _).trans sum_p2.2⟩
end KsIndex.AlphaRemarkTrial.Cache27904
