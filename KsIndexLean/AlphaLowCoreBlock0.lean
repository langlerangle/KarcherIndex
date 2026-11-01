module

public import KsIndexLean.AlphaLowModeSumAssembly
public import KsIndexLean.AlphaLowBlockCertificate0

@[expose] public section

namespace KsIndex.AlphaRemarkTrial.Cache0
theorem core_center (n : ℤ) :
    lowLinearNumerator (Finset.Ico (-16385) (-16129)) n =
      blockLinearNumerator (-16385) n center := by
  apply (blockLinearNumerator_eq_core KsIndex.PositiveEnergyAlphaLowProd.valid
    (-16385) n center ?_ ?_).symm
  · intro i
    convert low_block_covered 0 256 (by norm_num) i using 1; norm_num
  · intro i
    simpa only [center, mode, show (-16385 : ℤ)+0 = -16385 by norm_num] using (checked i).1

theorem core_radius (n : ℤ) :
    lowLinearRadius (Finset.Ico (-16385) (-16129)) n =
      blockLinearRadius (-16385) n radius := by
  apply (blockLinearRadius_eq_core KsIndex.PositiveEnergyAlphaLowProd.valid
    (-16385) n radius ?_ ?_).symm
  · intro i
    convert low_block_covered 0 256 (by norm_num) i using 1; norm_num
  · intro i
    simpa only [radius, mode, show (-16385 : ℤ)+0 = -16385 by norm_num] using (checked i).2
theorem core_m2 :
    lowLinearNumerator (Finset.Ico (-16385) (-16129)) (-2) = -32080023927549133727023149812153451125143000332 ∧
    lowLinearRadius (Finset.Ico (-16385) (-16129)) (-2) = 124913758152107028912128493442915715041 :=
  ⟨(core_center _).trans sum_m2.1, (core_radius _).trans sum_m2.2⟩
theorem core_m1 :
    lowLinearNumerator (Finset.Ico (-16385) (-16129)) (-1) = 32078050406225435657970135810743102480396824924 ∧
    lowLinearRadius (Finset.Ico (-16385) (-16129)) (-1) = 124906073586710235781845530779012845221 :=
  ⟨(core_center _).trans sum_m1.1, (core_radius _).trans sum_m1.2⟩
theorem core_p1 :
    lowLinearNumerator (Finset.Ico (-16385) (-16129)) (1) = 32074104091954254357420263121267846700553034080 ∧
    lowLinearRadius (Finset.Ico (-16385) (-16129)) (1) = 124890707292105459120309115601614871575 :=
  ⟨(core_center _).trans sum_p1.1, (core_radius _).trans sum_p1.2⟩
theorem core_p2 :
    lowLinearNumerator (Finset.Ico (-16385) (-16129)) (2) = -32072131298917166446383338429599461340877377738 ∧
    lowLinearRadius (Finset.Ico (-16385) (-16129)) (2) = 124883025562548566750964415423359892368 :=
  ⟨(core_center _).trans sum_p2.1, (core_radius _).trans sum_p2.2⟩
end KsIndex.AlphaRemarkTrial.Cache0
