module

public import KsIndexLean.AlphaLowModeSumAssembly
public import KsIndexLean.AlphaLowBlockCertificate25344

@[expose] public section

namespace KsIndex.AlphaRemarkTrial.Cache25344
theorem core_center (n : ℤ) :
    lowLinearNumerator (Finset.Ico (8959) (9215)) n =
      blockLinearNumerator (8959) n center := by
  apply (blockLinearNumerator_eq_core KsIndex.PositiveEnergyAlphaLowProd.valid
    (8959) n center ?_ ?_).symm
  · intro i
    convert low_block_covered 25344 256 (by norm_num) i using 1; norm_num
  · intro i
    simpa only [center, mode, show (-16385 : ℤ)+25344 = 8959 by norm_num] using (checked i).1

theorem core_radius (n : ℤ) :
    lowLinearRadius (Finset.Ico (8959) (9215)) n =
      blockLinearRadius (8959) n radius := by
  apply (blockLinearRadius_eq_core KsIndex.PositiveEnergyAlphaLowProd.valid
    (8959) n radius ?_ ?_).symm
  · intro i
    convert low_block_covered 25344 256 (by norm_num) i using 1; norm_num
  · intro i
    simpa only [radius, mode, show (-16385 : ℤ)+25344 = 8959 by norm_num] using (checked i).2
theorem core_m2 :
    lowLinearNumerator (Finset.Ico (8959) (9215)) (-2) = 200523480181880528993774129434668656833692774610 ∧
    lowLinearRadius (Finset.Ico (8959) (9215)) (-2) = 304644462032204942277812978484426627146 :=
  ⟨(core_center _).trans sum_m2.1, (core_radius _).trans sum_m2.2⟩
theorem core_m1 :
    lowLinearNumerator (Finset.Ico (8959) (9215)) (-1) = -200545548439579228678781638236407048534435680159 ∧
    lowLinearRadius (Finset.Ico (8959) (9215)) (-1) = 304677989267856704184628072925630844342 :=
  ⟨(core_center _).trans sum_m1.1, (core_radius _).trans sum_m1.2⟩
theorem core_p1 :
    lowLinearNumerator (Finset.Ico (8959) (9215)) (1) = -200589699531247921672278839810982451268923296579 ∧
    lowLinearRadius (Finset.Ico (8959) (9215)) (1) = 304745065884267538176442239506882048388 :=
  ⟨(core_center _).trans sum_p1.1, (core_radius _).trans sum_p1.2⟩
theorem core_p2 :
    lowLinearNumerator (Finset.Ico (8959) (9215)) (2) = 200611782368427730914682349227946190084123406104 ∧
    lowLinearRadius (Finset.Ico (8959) (9215)) (2) = 304778615269903165195399983243415950830 :=
  ⟨(core_center _).trans sum_p2.1, (core_radius _).trans sum_p2.2⟩
end KsIndex.AlphaRemarkTrial.Cache25344
