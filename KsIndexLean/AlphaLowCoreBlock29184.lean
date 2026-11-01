module

public import KsIndexLean.AlphaLowModeSumAssembly
public import KsIndexLean.AlphaLowBlockCertificate29184

@[expose] public section

namespace KsIndex.AlphaRemarkTrial.Cache29184
theorem core_center (n : ℤ) :
    lowLinearNumerator (Finset.Ico (12799) (13055)) n =
      blockLinearNumerator (12799) n center := by
  apply (blockLinearNumerator_eq_core KsIndex.PositiveEnergyAlphaLowProd.valid
    (12799) n center ?_ ?_).symm
  · intro i
    convert low_block_covered 29184 256 (by norm_num) i using 1; norm_num
  · intro i
    simpa only [center, mode, show (-16385 : ℤ)+29184 = 12799 by norm_num] using (checked i).1

theorem core_radius (n : ℤ) :
    lowLinearRadius (Finset.Ico (12799) (13055)) n =
      blockLinearRadius (12799) n radius := by
  apply (blockLinearRadius_eq_core KsIndex.PositiveEnergyAlphaLowProd.valid
    (12799) n radius ?_ ?_).symm
  · intro i
    convert low_block_covered 29184 256 (by norm_num) i using 1; norm_num
  · intro i
    simpa only [radius, mode, show (-16385 : ℤ)+29184 = 12799 by norm_num] using (checked i).2
theorem core_m2 :
    lowLinearNumerator (Finset.Ico (12799) (13055)) (-2) = 119182807041224741576499326896077332836580911109 ∧
    lowLinearRadius (Finset.Ico (12799) (13055)) (-2) = 177440784844264821110615133723737470706 :=
  ⟨(core_center _).trans sum_m2.1, (core_radius _).trans sum_m2.2⟩
theorem core_m1 :
    lowLinearNumerator (Finset.Ico (12799) (13055)) (-1) = -119192026754090191996978195543259758676000935903 ∧
    lowLinearRadius (Finset.Ico (12799) (13055)) (-1) = 177454511288547635767919110589799704068 :=
  ⟨(core_center _).trans sum_m1.1, (core_radius _).trans sum_m1.2⟩
theorem core_p1 :
    lowLinearNumerator (Finset.Ico (12799) (13055)) (1) = -119210470459920196925192294996266230104158394826 ∧
    lowLinearRadius (Finset.Ico (12799) (13055)) (1) = 177481970549399812260507727460381882823 :=
  ⟨(core_center _).trans sum_p1.1, (core_radius _).trans sum_p1.2⟩
theorem core_p2 :
    lowLinearNumerator (Finset.Ico (12799) (13055)) (2) = 119219694453547146058404072355242944009320094244 ∧
    lowLinearRadius (Finset.Ico (12799) (13055)) (2) = 177495703366955360674338737181044705964 :=
  ⟨(core_center _).trans sum_p2.1, (core_radius _).trans sum_p2.2⟩
end KsIndex.AlphaRemarkTrial.Cache29184
