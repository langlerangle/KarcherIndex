module

public import KsIndexLean.AlphaLowModeSumAssembly
public import KsIndexLean.AlphaLowBlockCertificate32000

@[expose] public section

namespace KsIndex.AlphaRemarkTrial.Cache32000
theorem core_center (n : ℤ) :
    lowLinearNumerator (Finset.Ico (15615) (15871)) n =
      blockLinearNumerator (15615) n center := by
  apply (blockLinearNumerator_eq_core KsIndex.PositiveEnergyAlphaLowProd.valid
    (15615) n center ?_ ?_).symm
  · intro i
    convert low_block_covered 32000 256 (by norm_num) i using 1; norm_num
  · intro i
    simpa only [center, mode, show (-16385 : ℤ)+32000 = 15615 by norm_num] using (checked i).1

theorem core_radius (n : ℤ) :
    lowLinearRadius (Finset.Ico (15615) (15871)) n =
      blockLinearRadius (15615) n radius := by
  apply (blockLinearRadius_eq_core KsIndex.PositiveEnergyAlphaLowProd.valid
    (15615) n radius ?_ ?_).symm
  · intro i
    convert low_block_covered 32000 256 (by norm_num) i using 1; norm_num
  · intro i
    simpa only [radius, mode, show (-16385 : ℤ)+32000 = 15615 by norm_num] using (checked i).2
theorem core_m2 :
    lowLinearNumerator (Finset.Ico (15615) (15871)) (-2) = 89119690228058937505138759771630975654060024747 ∧
    lowLinearRadius (Finset.Ico (15615) (15871)) (-2) = 131186481821504006976089344875245633457 :=
  ⟨(core_center _).trans sum_m2.1, (core_radius _).trans sum_m2.2⟩
theorem core_m1 :
    lowLinearNumerator (Finset.Ico (15615) (15871)) (-1) = -89125351086124767408963103059133686784574113631 ∧
    lowLinearRadius (Finset.Ico (15615) (15871)) (-1) = 131194814761103084307506953758874604940 :=
  ⟨(core_center _).trans sum_m1.1, (core_radius _).trans sum_m1.2⟩
theorem core_p1 :
    lowLinearNumerator (Finset.Ico (15615) (15871)) (1) = -89136674960034926033400051674517355171966964358 ∧
    lowLinearRadius (Finset.Ico (15615) (15871)) (1) = 131211483816614882568636534755327738557 :=
  ⟨(core_center _).trans sum_p1.1, (core_radius _).trans sum_p1.2⟩
theorem core_p2 :
    lowLinearNumerator (Finset.Ico (15615) (15871)) (2) = 89142337976153442072898428301319048626267329460 ∧
    lowLinearRadius (Finset.Ico (15615) (15871)) (2) = 131219819932931215837232399142336117692 :=
  ⟨(core_center _).trans sum_p2.1, (core_radius _).trans sum_p2.2⟩
end KsIndex.AlphaRemarkTrial.Cache32000
