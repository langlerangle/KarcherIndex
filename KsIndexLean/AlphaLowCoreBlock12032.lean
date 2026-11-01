module

public import KsIndexLean.AlphaLowModeSumAssembly
public import KsIndexLean.AlphaLowBlockCertificate12032

@[expose] public section

namespace KsIndex.AlphaRemarkTrial.Cache12032
theorem core_center (n : ℤ) :
    lowLinearNumerator (Finset.Ico (-4353) (-4097)) n =
      blockLinearNumerator (-4353) n center := by
  apply (blockLinearNumerator_eq_core KsIndex.PositiveEnergyAlphaLowProd.valid
    (-4353) n center ?_ ?_).symm
  · intro i
    convert low_block_covered 12032 256 (by norm_num) i using 1; norm_num
  · intro i
    simpa only [center, mode, show (-16385 : ℤ)+12032 = -4353 by norm_num] using (checked i).1

theorem core_radius (n : ℤ) :
    lowLinearRadius (Finset.Ico (-4353) (-4097)) n =
      blockLinearRadius (-4353) n radius := by
  apply (blockLinearRadius_eq_core KsIndex.PositiveEnergyAlphaLowProd.valid
    (-4353) n radius ?_ ?_).symm
  · intro i
    convert low_block_covered 12032 256 (by norm_num) i using 1; norm_num
  · intro i
    simpa only [radius, mode, show (-16385 : ℤ)+12032 = -4353 by norm_num] using (checked i).2
theorem core_m2 :
    lowLinearNumerator (Finset.Ico (-4353) (-4097)) (-2) = -184704760812337249972518357158269057255889390996 ∧
    lowLinearRadius (Finset.Ico (-4353) (-4097)) (-2) = 988372788574390118611423020147838632946 :=
  ⟨(core_center _).trans sum_m2.1, (core_radius _).trans sum_m2.2⟩
theorem core_m1 :
    lowLinearNumerator (Finset.Ico (-4353) (-4097)) (-1) = 184661002923794891344723841088452273002672157397 ∧
    lowLinearRadius (Finset.Ico (-4353) (-4097)) (-1) = 988138616964807676526844094169621268665 :=
  ⟨(core_center _).trans sum_m1.1, (core_radius _).trans sum_m1.2⟩
theorem core_p1 :
    lowLinearNumerator (Finset.Ico (-4353) (-4097)) (1) = 184573549335627033902724630986901932528065215311 ∧
    lowLinearRadius (Finset.Ico (-4353) (-4097)) (1) = 987670606578378775875969941280596689688 :=
  ⟨(core_center _).trans sum_p1.1, (core_radius _).trans sum_p1.2⟩
theorem core_p2 :
    lowLinearNumerator (Finset.Ico (-4353) (-4097)) (2) = -184529853606538450769738220244967833245454514407 ∧
    lowLinearRadius (Finset.Ico (-4353) (-4097)) (2) = 987436767643834249831458672702557637069 :=
  ⟨(core_center _).trans sum_p2.1, (core_radius _).trans sum_p2.2⟩
end KsIndex.AlphaRemarkTrial.Cache12032
