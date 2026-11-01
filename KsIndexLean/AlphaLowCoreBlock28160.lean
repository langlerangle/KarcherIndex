module

public import KsIndexLean.AlphaLowModeSumAssembly
public import KsIndexLean.AlphaLowBlockCertificate28160

@[expose] public section

namespace KsIndex.AlphaRemarkTrial.Cache28160
theorem core_center (n : ℤ) :
    lowLinearNumerator (Finset.Ico (11775) (12031)) n =
      blockLinearNumerator (11775) n center := by
  apply (blockLinearNumerator_eq_core KsIndex.PositiveEnergyAlphaLowProd.valid
    (11775) n center ?_ ?_).symm
  · intro i
    convert low_block_covered 28160 256 (by norm_num) i using 1; norm_num
  · intro i
    simpa only [center, mode, show (-16385 : ℤ)+28160 = 11775 by norm_num] using (checked i).1

theorem core_radius (n : ℤ) :
    lowLinearRadius (Finset.Ico (11775) (12031)) n =
      blockLinearRadius (11775) n radius := by
  apply (blockLinearRadius_eq_core KsIndex.PositiveEnergyAlphaLowProd.valid
    (11775) n radius ?_ ?_).symm
  · intro i
    convert low_block_covered 28160 256 (by norm_num) i using 1; norm_num
  · intro i
    simpa only [radius, mode, show (-16385 : ℤ)+28160 = 11775 by norm_num] using (checked i).2
theorem core_m2 :
    lowLinearNumerator (Finset.Ico (11775) (12031)) (-2) = 134616304027376341173178875118478005083848357892 ∧
    lowLinearRadius (Finset.Ico (11775) (12031)) (-2) = 201371278730465238320481719626567576357 :=
  ⟨(core_center _).trans sum_m2.1, (core_radius _).trans sum_m2.2⟩
theorem core_m1 :
    lowLinearNumerator (Finset.Ico (11775) (12031)) (-1) = -134627613599726396236822395220778484704761556305 ∧
    lowLinearRadius (Finset.Ico (11775) (12031)) (-1) = 201388196652149972181442251987273574187 :=
  ⟨(core_center _).trans sum_m1.1, (core_radius _).trans sum_m1.2⟩
theorem core_p1 :
    lowLinearNumerator (Finset.Ico (11775) (12031)) (1) = -134650238446537634493404771050048699536355548789 ∧
    lowLinearRadius (Finset.Ico (11775) (12031)) (1) = 201422041025292286436199295081632796407 :=
  ⟨(core_center _).trans sum_p1.1, (core_radius _).trans sum_p1.2⟩
theorem core_p2 :
    lowLinearNumerator (Finset.Ico (11775) (12031)) (2) = 134661553721957240530123239036461113559315489713 ∧
    lowLinearRadius (Finset.Ico (11775) (12031)) (2) = 201438967478183572183753151446578638186 :=
  ⟨(core_center _).trans sum_p2.1, (core_radius _).trans sum_p2.2⟩
end KsIndex.AlphaRemarkTrial.Cache28160
