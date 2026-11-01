module

public import KsIndexLean.AlphaLowModeSumAssembly
public import KsIndexLean.AlphaLowBlockCertificate18432

@[expose] public section

namespace KsIndex.AlphaRemarkTrial.Cache18432
theorem core_center (n : ℤ) :
    lowLinearNumerator (Finset.Ico (2047) (2303)) n =
      blockLinearNumerator (2047) n center := by
  apply (blockLinearNumerator_eq_core KsIndex.PositiveEnergyAlphaLowProd.valid
    (2047) n center ?_ ?_).symm
  · intro i
    convert low_block_covered 18432 256 (by norm_num) i using 1; norm_num
  · intro i
    simpa only [center, mode, show (-16385 : ℤ)+18432 = 2047 by norm_num] using (checked i).1

theorem core_radius (n : ℤ) :
    lowLinearRadius (Finset.Ico (2047) (2303)) n =
      blockLinearRadius (2047) n radius := by
  apply (blockLinearRadius_eq_core KsIndex.PositiveEnergyAlphaLowProd.valid
    (2047) n radius ?_ ?_).symm
  · intro i
    convert low_block_covered 18432 256 (by norm_num) i using 1; norm_num
  · intro i
    simpa only [radius, mode, show (-16385 : ℤ)+18432 = 2047 by norm_num] using (checked i).2
theorem core_m2 :
    lowLinearNumerator (Finset.Ico (2047) (2303)) (-2) = 1665619547551720626743788873034123259346402686299 ∧
    lowLinearRadius (Finset.Ico (2047) (2303)) (-2) = 2744738770424925903123882575765429764522 :=
  ⟨(core_center _).trans sum_m2.1, (core_radius _).trans sum_m2.2⟩
theorem core_m1 :
    lowLinearNumerator (Finset.Ico (2047) (2303)) (-1) = -1666387196581979558559777746436141123520475723737 ∧
    lowLinearRadius (Finset.Ico (2047) (2303)) (-1) = 2746003844827032466781926884121439601278 :=
  ⟨(core_center _).trans sum_m1.1, (core_radius _).trans sum_m1.2⟩
theorem core_p1 :
    lowLinearNumerator (Finset.Ico (2047) (2303)) (1) = -1667924621818979118349823852496974323815930579156 ∧
    lowLinearRadius (Finset.Ico (2047) (2303)) (1) = 2748537499414051747176921976308942291612 :=
  ⟨(core_center _).trans sum_p1.1, (core_radius _).trans sum_p1.2⟩
theorem core_p2 :
    lowLinearNumerator (Finset.Ico (2047) (2303)) (2) = 1668694399993719145200206865176646937688893613216 ∧
    lowLinearRadius (Finset.Ico (2047) (2303)) (2) = 2749806082842618165630462408596680196097 :=
  ⟨(core_center _).trans sum_p2.1, (core_radius _).trans sum_p2.2⟩
end KsIndex.AlphaRemarkTrial.Cache18432
