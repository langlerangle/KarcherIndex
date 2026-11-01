module

public import KsIndexLean.AlphaLowModeSumAssembly
public import KsIndexLean.AlphaLowBlockCertificate10496

@[expose] public section

namespace KsIndex.AlphaRemarkTrial.Cache10496
theorem core_center (n : ℤ) :
    lowLinearNumerator (Finset.Ico (-5889) (-5633)) n =
      blockLinearNumerator (-5889) n center := by
  apply (blockLinearNumerator_eq_core KsIndex.PositiveEnergyAlphaLowProd.valid
    (-5889) n center ?_ ?_).symm
  · intro i
    convert low_block_covered 10496 256 (by norm_num) i using 1; norm_num
  · intro i
    simpa only [center, mode, show (-16385 : ℤ)+10496 = -5889 by norm_num] using (checked i).1

theorem core_radius (n : ℤ) :
    lowLinearRadius (Finset.Ico (-5889) (-5633)) n =
      blockLinearRadius (-5889) n radius := by
  apply (blockLinearRadius_eq_core KsIndex.PositiveEnergyAlphaLowProd.valid
    (-5889) n radius ?_ ?_).symm
  · intro i
    convert low_block_covered 10496 256 (by norm_num) i using 1; norm_num
  · intro i
    simpa only [radius, mode, show (-16385 : ℤ)+10496 = -5889 by norm_num] using (checked i).2
theorem core_m2 :
    lowLinearNumerator (Finset.Ico (-5889) (-5633)) (-2) = -124194126706634689592509805798609857935816902534 ∧
    lowLinearRadius (Finset.Ico (-5889) (-5633)) (-2) = 613594172954456626505184955520733471543 :=
  ⟨(core_center _).trans sum_m2.1, (core_radius _).trans sum_m2.2⟩
theorem core_m1 :
    lowLinearNumerator (Finset.Ico (-5889) (-5633)) (-1) = 124172557110059008535800944001362479414855382236 ∧
    lowLinearRadius (Finset.Ico (-5889) (-5633)) (-1) = 613487601704722382998206880186642018407 :=
  ⟨(core_center _).trans sum_m1.1, (core_radius _).trans sum_m1.2⟩
theorem core_p1 :
    lowLinearNumerator (Finset.Ico (-5889) (-5633)) (1) = 124129440389587169873358155837551959164457754265 ∧
    lowLinearRadius (Finset.Ico (-5889) (-5633)) (1) = 613274570243029072712447750782677642141 :=
  ⟨(core_center _).trans sum_p1.1, (core_radius _).trans sum_p1.2⟩
theorem core_p2 :
    lowLinearNumerator (Finset.Ico (-5889) (-5633)) (2) = -124107893257886559942146295270017098324517057784 ∧
    lowLinearRadius (Finset.Ico (-5889) (-5633)) (2) = 613168109992506530186534027634374602761 :=
  ⟨(core_center _).trans sum_p2.1, (core_radius _).trans sum_p2.2⟩
end KsIndex.AlphaRemarkTrial.Cache10496
