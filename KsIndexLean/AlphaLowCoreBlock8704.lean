module

public import KsIndexLean.AlphaLowModeSumAssembly
public import KsIndexLean.AlphaLowBlockCertificate8704

@[expose] public section

namespace KsIndex.AlphaRemarkTrial.Cache8704
theorem core_center (n : ℤ) :
    lowLinearNumerator (Finset.Ico (-7681) (-7425)) n =
      blockLinearNumerator (-7681) n center := by
  apply (blockLinearNumerator_eq_core KsIndex.PositiveEnergyAlphaLowProd.valid
    (-7681) n center ?_ ?_).symm
  · intro i
    convert low_block_covered 8704 256 (by norm_num) i using 1; norm_num
  · intro i
    simpa only [center, mode, show (-16385 : ℤ)+8704 = -7681 by norm_num] using (checked i).1

theorem core_radius (n : ℤ) :
    lowLinearRadius (Finset.Ico (-7681) (-7425)) n =
      blockLinearRadius (-7681) n radius := by
  apply (blockLinearRadius_eq_core KsIndex.PositiveEnergyAlphaLowProd.valid
    (-7681) n radius ?_ ?_).symm
  · intro i
    convert low_block_covered 8704 256 (by norm_num) i using 1; norm_num
  · intro i
    simpa only [radius, mode, show (-16385 : ℤ)+8704 = -7681 by norm_num] using (checked i).2
theorem core_m2 :
    lowLinearNumerator (Finset.Ico (-7681) (-7425)) (-2) = -87532000053712425153870725133731203867233649161 ∧
    lowLinearRadius (Finset.Ico (-7681) (-7425)) (-2) = 404784336637048226900763407027140958359 :=
  ⟨(core_center _).trans sum_m2.1, (core_radius _).trans sum_m2.2⟩
theorem core_m1 :
    lowLinearNumerator (Finset.Ico (-7681) (-7425)) (-1) = 87520406932356373810703450761175467037795907349 ∧
    lowLinearRadius (Finset.Ico (-7681) (-7425)) (-1) = 404730724003091941800112698417335286056 :=
  ⟨(core_center _).trans sum_m1.1, (core_radius _).trans sum_m1.2⟩
theorem core_p1 :
    lowLinearNumerator (Finset.Ico (-7681) (-7425)) (1) = 87497229900748699432248333186641869103253553298 ∧
    lowLinearRadius (Finset.Ico (-7681) (-7425)) (1) = 404623541333097994450310729222490974415 :=
  ⟨(core_center _).trans sum_p1.1, (core_radius _).trans sum_p1.2⟩
theorem core_p2 :
    lowLinearNumerator (Finset.Ico (-7681) (-7425)) (2) = -87485645988057660681582765303324125412012277872 ∧
    lowLinearRadius (Finset.Ico (-7681) (-7425)) (2) = 404569971285778688021007993113354655748 :=
  ⟨(core_center _).trans sum_p2.1, (core_radius _).trans sum_p2.2⟩
end KsIndex.AlphaRemarkTrial.Cache8704
