module

public import KsIndexLean.AlphaLowModeSumAssembly
public import KsIndexLean.AlphaLowBlockCertificate18176

@[expose] public section

namespace KsIndex.AlphaRemarkTrial.Cache18176
theorem core_center (n : ℤ) :
    lowLinearNumerator (Finset.Ico (1791) (2047)) n =
      blockLinearNumerator (1791) n center := by
  apply (blockLinearNumerator_eq_core KsIndex.PositiveEnergyAlphaLowProd.valid
    (1791) n center ?_ ?_).symm
  · intro i
    convert low_block_covered 18176 256 (by norm_num) i using 1; norm_num
  · intro i
    simpa only [center, mode, show (-16385 : ℤ)+18176 = 1791 by norm_num] using (checked i).1

theorem core_radius (n : ℤ) :
    lowLinearRadius (Finset.Ico (1791) (2047)) n =
      blockLinearRadius (1791) n radius := by
  apply (blockLinearRadius_eq_core KsIndex.PositiveEnergyAlphaLowProd.valid
    (1791) n radius ?_ ?_).symm
  · intro i
    convert low_block_covered 18176 256 (by norm_num) i using 1; norm_num
  · intro i
    simpa only [radius, mode, show (-16385 : ℤ)+18176 = 1791 by norm_num] using (checked i).2
theorem core_m2 :
    lowLinearNumerator (Finset.Ico (1791) (2047)) (-2) = 2006485093826487475026069225725472592043357860385 ∧
    lowLinearRadius (Finset.Ico (1791) (2047)) (-2) = 3329846268155159735079495143121268970609 :=
  ⟨(core_center _).trans sum_m2.1, (core_radius _).trans sum_m2.2⟩
theorem core_m1 :
    lowLinearNumerator (Finset.Ico (1791) (2047)) (-1) = -2007533998499547712599854881533528101698624583831 ∧
    lowLinearRadius (Finset.Ico (1791) (2047)) (-1) = 3331587114177902168421901344625977557593 :=
  ⟨(core_center _).trans sum_m1.1, (core_radius _).trans sum_m1.2⟩
theorem core_p1 :
    lowLinearNumerator (Finset.Ico (1791) (2047)) (1) = -2009635106121295154980294943854430884405765506447 ∧
    lowLinearRadius (Finset.Ico (1791) (2047)) (1) = 3335074280759420075964314334051454149591 :=
  ⟨(core_center _).trans sum_p1.1, (core_radius _).trans sum_p1.2⟩
theorem core_p2 :
    lowLinearNumerator (Finset.Ico (1791) (2047)) (2) = 2010687312534062860402980123797233235798643890732 ∧
    lowLinearRadius (Finset.Ico (1791) (2047)) (2) = 3336820607068412632969811202321006858651 :=
  ⟨(core_center _).trans sum_p2.1, (core_radius _).trans sum_p2.2⟩
end KsIndex.AlphaRemarkTrial.Cache18176
