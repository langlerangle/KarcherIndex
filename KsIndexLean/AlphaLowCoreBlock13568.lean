module

public import KsIndexLean.AlphaLowModeSumAssembly
public import KsIndexLean.AlphaLowBlockCertificate13568

@[expose] public section

namespace KsIndex.AlphaRemarkTrial.Cache13568
theorem core_center (n : ℤ) :
    lowLinearNumerator (Finset.Ico (-2817) (-2561)) n =
      blockLinearNumerator (-2817) n center := by
  apply (blockLinearNumerator_eq_core KsIndex.PositiveEnergyAlphaLowProd.valid
    (-2817) n center ?_ ?_).symm
  · intro i
    convert low_block_covered 13568 256 (by norm_num) i using 1; norm_num
  · intro i
    simpa only [center, mode, show (-16385 : ℤ)+13568 = -2817 by norm_num] using (checked i).1

theorem core_radius (n : ℤ) :
    lowLinearRadius (Finset.Ico (-2817) (-2561)) n =
      blockLinearRadius (-2817) n radius := by
  apply (blockLinearRadius_eq_core KsIndex.PositiveEnergyAlphaLowProd.valid
    (-2817) n radius ?_ ?_).symm
  · intro i
    convert low_block_covered 13568 256 (by norm_num) i using 1; norm_num
  · intro i
    simpa only [radius, mode, show (-16385 : ℤ)+13568 = -2817 by norm_num] using (checked i).2
theorem core_m2 :
    lowLinearNumerator (Finset.Ico (-2817) (-2561)) (-2) = -326732376054082234288288084884700278320299956244 ∧
    lowLinearRadius (Finset.Ico (-2817) (-2561)) (-2) = 1981943605629652379491516753825571860155 :=
  ⟨(core_center _).trans sum_m2.1, (core_radius _).trans sum_m2.2⟩
theorem core_m1 :
    lowLinearNumerator (Finset.Ico (-2817) (-2561)) (-1) = 326610616849577727783294061632767984388373742141 ∧
    lowLinearRadius (Finset.Ico (-2817) (-2561)) (-1) = 1981204857809366612974469317731580707673 :=
  ⟨(core_center _).trans sum_m1.1, (core_radius _).trans sum_m1.2⟩
theorem core_p1 :
    lowLinearNumerator (Finset.Ico (-2817) (-2561)) (1) = 326367370690088675163294684546372208670152379777 ∧
    lowLinearRadius (Finset.Ico (-2817) (-2561)) (1) = 1979729014346040604506369077798069077206 :=
  ⟨(core_center _).trans sum_p1.1, (core_radius _).trans sum_p1.2⟩
theorem core_p2 :
    lowLinearNumerator (Finset.Ico (-2817) (-2561)) (2) = -326245883532113207449850569207991798411137080513 ∧
    lowLinearRadius (Finset.Ico (-2817) (-2561)) (2) = 1978991917470857693238365828272246228107 :=
  ⟨(core_center _).trans sum_p2.1, (core_radius _).trans sum_p2.2⟩
end KsIndex.AlphaRemarkTrial.Cache13568
