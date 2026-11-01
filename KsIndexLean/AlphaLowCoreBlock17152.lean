module

public import KsIndexLean.AlphaLowModeSumAssembly
public import KsIndexLean.AlphaLowBlockCertificate17152

@[expose] public section

namespace KsIndex.AlphaRemarkTrial.Cache17152
theorem core_center (n : ℤ) :
    lowLinearNumerator (Finset.Ico (767) (1023)) n =
      blockLinearNumerator (767) n center := by
  apply (blockLinearNumerator_eq_core KsIndex.PositiveEnergyAlphaLowProd.valid
    (767) n center ?_ ?_).symm
  · intro i
    convert low_block_covered 17152 256 (by norm_num) i using 1; norm_num
  · intro i
    simpa only [center, mode, show (-16385 : ℤ)+17152 = 767 by norm_num] using (checked i).1

theorem core_radius (n : ℤ) :
    lowLinearRadius (Finset.Ico (767) (1023)) n =
      blockLinearRadius (767) n radius := by
  apply (blockLinearRadius_eq_core KsIndex.PositiveEnergyAlphaLowProd.valid
    (767) n radius ?_ ?_).symm
  · intro i
    convert low_block_covered 17152 256 (by norm_num) i using 1; norm_num
  · intro i
    simpa only [radius, mode, show (-16385 : ℤ)+17152 = 767 by norm_num] using (checked i).2
theorem core_m2 :
    lowLinearNumerator (Finset.Ico (767) (1023)) (-2) = 6282039806873447612337120143071606027757464008180 ∧
    lowLinearRadius (Finset.Ico (767) (1023)) (-2) = 10882783039683385685548485201335213318051 :=
  ⟨(core_center _).trans sum_m2.1, (core_radius _).trans sum_m2.2⟩
theorem core_m1 :
    lowLinearNumerator (Finset.Ico (767) (1023)) (-1) = -6289171917959202622821008977060171538383309328519 ∧
    lowLinearRadius (Finset.Ico (767) (1023)) (-1) = 10895143132861427963826902436390151540762 :=
  ⟨(core_center _).trans sum_m1.1, (core_radius _).trans sum_m1.2⟩
theorem core_p1 :
    lowLinearNumerator (Finset.Ico (767) (1023)) (1) = -6303485169190136312068630714829670115093054709239 ∧
    lowLinearRadius (Finset.Ico (767) (1023)) (1) = 10919948319406863624831502428016784334719 :=
  ⟨(core_center _).trans sum_p1.1, (core_radius _).trans sum_p1.2⟩
theorem core_p2 :
    lowLinearNumerator (Finset.Ico (767) (1023)) (2) = 6310666422576352616285020898161430495554767843290 ∧
    lowLinearRadius (Finset.Ico (767) (1023)) (2) = 10932393609168940333048215890488066467495 :=
  ⟨(core_center _).trans sum_p2.1, (core_radius _).trans sum_p2.2⟩
end KsIndex.AlphaRemarkTrial.Cache17152
