module

public import KsIndexLean.AlphaLowModeSumAssembly
public import KsIndexLean.AlphaLowBlockCertificate24576

@[expose] public section

namespace KsIndex.AlphaRemarkTrial.Cache24576
theorem core_center (n : ℤ) :
    lowLinearNumerator (Finset.Ico (8191) (8447)) n =
      blockLinearNumerator (8191) n center := by
  apply (blockLinearNumerator_eq_core KsIndex.PositiveEnergyAlphaLowProd.valid
    (8191) n center ?_ ?_).symm
  · intro i
    convert low_block_covered 24576 256 (by norm_num) i using 1; norm_num
  · intro i
    simpa only [center, mode, show (-16385 : ℤ)+24576 = 8191 by norm_num] using (checked i).1

theorem core_radius (n : ℤ) :
    lowLinearRadius (Finset.Ico (8191) (8447)) n =
      blockLinearRadius (8191) n radius := by
  apply (blockLinearRadius_eq_core KsIndex.PositiveEnergyAlphaLowProd.valid
    (8191) n radius ?_ ?_).symm
  · intro i
    convert low_block_covered 24576 256 (by norm_num) i using 1; norm_num
  · intro i
    simpa only [radius, mode, show (-16385 : ℤ)+24576 = 8191 by norm_num] using (checked i).2
theorem core_m2 :
    lowLinearNumerator (Finset.Ico (8191) (8447)) (-2) = 228458350868937867771245615720014144007101697428 ∧
    lowLinearRadius (Finset.Ico (8191) (8447)) (-2) = 348844808028213566209328105690312912298 :=
  ⟨(core_center _).trans sum_m2.1, (core_radius _).trans sum_m2.2⟩
theorem core_m1 :
    lowLinearNumerator (Finset.Ico (8191) (8447)) (-1) = -228485815172757640810205733358551226077846475425 ∧
    lowLinearRadius (Finset.Ico (8191) (8447)) (-1) = 348886744875960415148162829948623239619 :=
  ⟨(core_center _).trans sum_m1.1, (core_radius _).trans sum_m1.2⟩
theorem core_p1 :
    lowLinearNumerator (Finset.Ico (8191) (8447)) (1) = -228540763596585217340365208653169232685986764617 ∧
    lowLinearRadius (Finset.Ico (8191) (8447)) (1) = 348970648830084389140687275361589400770 :=
  ⟨(core_center _).trans sum_p1.1, (core_radius _).trans sum_p1.2⟩
theorem core_p2 :
    lowLinearNumerator (Finset.Ico (8191) (8447)) (2) = 228568247721359930164112667812483683468597933331 ∧
    lowLinearRadius (Finset.Ico (8191) (8447)) (2) = 349012615943740451922201506637169331603 :=
  ⟨(core_center _).trans sum_p2.1, (core_radius _).trans sum_p2.2⟩
end KsIndex.AlphaRemarkTrial.Cache24576
