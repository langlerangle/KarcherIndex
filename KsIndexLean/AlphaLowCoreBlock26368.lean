module

public import KsIndexLean.AlphaLowModeSumAssembly
public import KsIndexLean.AlphaLowBlockCertificate26368

@[expose] public section

namespace KsIndex.AlphaRemarkTrial.Cache26368
theorem core_center (n : ℤ) :
    lowLinearNumerator (Finset.Ico (9983) (10239)) n =
      blockLinearNumerator (9983) n center := by
  apply (blockLinearNumerator_eq_core KsIndex.PositiveEnergyAlphaLowProd.valid
    (9983) n center ?_ ?_).symm
  · intro i
    convert low_block_covered 26368 256 (by norm_num) i using 1; norm_num
  · intro i
    simpa only [center, mode, show (-16385 : ℤ)+26368 = 9983 by norm_num] using (checked i).1

theorem core_radius (n : ℤ) :
    lowLinearRadius (Finset.Ico (9983) (10239)) n =
      blockLinearRadius (9983) n radius := by
  apply (blockLinearRadius_eq_core KsIndex.PositiveEnergyAlphaLowProd.valid
    (9983) n radius ?_ ?_).symm
  · intro i
    convert low_block_covered 26368 256 (by norm_num) i using 1; norm_num
  · intro i
    simpa only [radius, mode, show (-16385 : ℤ)+26368 = 9983 by norm_num] using (checked i).2
theorem core_m2 :
    lowLinearNumerator (Finset.Ico (9983) (10239)) (-2) = 171273887979478367521448516694320932223152162477 ∧
    lowLinearRadius (Finset.Ico (9983) (10239)) (-2) = 258618614726222575778536295336904221966 :=
  ⟨(core_center _).trans sum_m2.1, (core_radius _).trans sum_m2.2⟩
theorem core_m1 :
    lowLinearNumerator (Finset.Ico (9983) (10239)) (-1) = -171290827906665622328454673819482758782648395706 ∧
    lowLinearRadius (Finset.Ico (9983) (10239)) (-1) = 258644193604469317174672225844631963963 :=
  ⟨(core_center _).trans sum_m1.1, (core_radius _).trans sum_m1.2⟩
theorem core_p1 :
    lowLinearNumerator (Finset.Ico (9983) (10239)) (1) = -171324717816276743160559988089573214514391672077 ∧
    lowLinearRadius (Finset.Ico (9983) (10239)) (1) = 258695366544172173082340016092283560937 :=
  ⟨(core_center _).trans sum_p1.1, (core_radius _).trans sum_p1.2⟩
theorem core_p2 :
    lowLinearNumerator (Finset.Ico (9983) (10239)) (2) = 171341667800690448325020889241413805156798707630 ∧
    lowLinearRadius (Finset.Ico (9983) (10239)) (2) = 258720960608632914737251871526892783667 :=
  ⟨(core_center _).trans sum_p2.1, (core_radius _).trans sum_p2.2⟩
end KsIndex.AlphaRemarkTrial.Cache26368
