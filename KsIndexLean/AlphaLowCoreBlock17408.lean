module

public import KsIndexLean.AlphaLowModeSumAssembly
public import KsIndexLean.AlphaLowBlockCertificate17408

@[expose] public section

namespace KsIndex.AlphaRemarkTrial.Cache17408
theorem core_center (n : ℤ) :
    lowLinearNumerator (Finset.Ico (1023) (1279)) n =
      blockLinearNumerator (1023) n center := by
  apply (blockLinearNumerator_eq_core KsIndex.PositiveEnergyAlphaLowProd.valid
    (1023) n center ?_ ?_).symm
  · intro i
    convert low_block_covered 17408 256 (by norm_num) i using 1; norm_num
  · intro i
    simpa only [center, mode, show (-16385 : ℤ)+17408 = 1023 by norm_num] using (checked i).1

theorem core_radius (n : ℤ) :
    lowLinearRadius (Finset.Ico (1023) (1279)) n =
      blockLinearRadius (1023) n radius := by
  apply (blockLinearRadius_eq_core KsIndex.PositiveEnergyAlphaLowProd.valid
    (1023) n radius ?_ ?_).symm
  · intro i
    convert low_block_covered 17408 256 (by norm_num) i using 1; norm_num
  · intro i
    simpa only [radius, mode, show (-16385 : ℤ)+17408 = 1023 by norm_num] using (checked i).2
theorem core_m2 :
    lowLinearNumerator (Finset.Ico (1023) (1279)) (-2) = 4303091364569578186094040179441107525878530142327 ∧
    lowLinearRadius (Finset.Ico (1023) (1279)) (-2) = 7349464591711430973750142312297382838903 :=
  ⟨(core_center _).trans sum_m2.1, (core_radius _).trans sum_m2.2⟩
theorem core_m1 :
    lowLinearNumerator (Finset.Ico (1023) (1279)) (-1) = -4306865337023390425271118302783418141114838047103 ∧
    lowLinearRadius (Finset.Ico (1023) (1279)) (-1) = 7355911825964217756742402736026942515177 :=
  ⟨(core_center _).trans sum_m1.1, (core_radius _).trans sum_m1.2⟩
theorem core_p1 :
    lowLinearNumerator (Finset.Ico (1023) (1279)) (1) = -4314433258843138006644620278692229049079996699032 ∧
    lowLinearRadius (Finset.Ico (1023) (1279)) (1) = 7368840429642022326494211211462635434680 :=
  ⟨(core_center _).trans sum_p1.1, (core_radius _).trans sum_p1.2⟩
theorem core_p2 :
    lowLinearNumerator (Finset.Ico (1023) (1279)) (2) = 4318227243633545341771286870827415694765548923364 ∧
    lowLinearRadius (Finset.Ico (1023) (1279)) (2) = 7375321859611582549759564984335260322177 :=
  ⟨(core_center _).trans sum_p2.1, (core_radius _).trans sum_p2.2⟩
end KsIndex.AlphaRemarkTrial.Cache17408
