module

public import KsIndexLean.AlphaLowModeSumAssembly
public import KsIndexLean.AlphaLowBlockCertificate27392

@[expose] public section

namespace KsIndex.AlphaRemarkTrial.Cache27392
theorem core_center (n : ℤ) :
    lowLinearNumerator (Finset.Ico (11007) (11263)) n =
      blockLinearNumerator (11007) n center := by
  apply (blockLinearNumerator_eq_core KsIndex.PositiveEnergyAlphaLowProd.valid
    (11007) n center ?_ ?_).symm
  · intro i
    convert low_block_covered 27392 256 (by norm_num) i using 1; norm_num
  · intro i
    simpa only [center, mode, show (-16385 : ℤ)+27392 = 11007 by norm_num] using (checked i).1

theorem core_radius (n : ℤ) :
    lowLinearRadius (Finset.Ico (11007) (11263)) n =
      blockLinearRadius (11007) n radius := by
  apply (blockLinearRadius_eq_core KsIndex.PositiveEnergyAlphaLowProd.valid
    (11007) n radius ?_ ?_).symm
  · intro i
    convert low_block_covered 27392 256 (by norm_num) i using 1; norm_num
  · intro i
    simpa only [radius, mode, show (-16385 : ℤ)+27392 = 11007 by norm_num] using (checked i).2
theorem core_m2 :
    lowLinearNumerator (Finset.Ico (11007) (11263)) (-2) = 148540984488823808857704896252836050541916679432 ∧
    lowLinearRadius (Finset.Ico (11007) (11263)) (-2) = 223054007193000363172749073584056892576 :=
  ⟨(core_center _).trans sum_m2.1, (core_radius _).trans sum_m2.2⟩
theorem core_m1 :
    lowLinearNumerator (Finset.Ico (11007) (11263)) (-1) = -148554324753087008696548322489210811545580671383 ∧
    lowLinearRadius (Finset.Ico (11007) (11263)) (-1) = 223074039421385552665332293242476578535 :=
  ⟨(core_center _).trans sum_m1.1, (core_radius _).trans sum_m1.2⟩
theorem core_p1 :
    lowLinearNumerator (Finset.Ico (11007) (11263)) (1) = -148581012471647753412801111809461948555439340641 ∧
    lowLinearRadius (Finset.Ico (11007) (11263)) (1) = 223114114675001596166144139649067426052 :=
  ⟨(core_center _).trans sum_p1.1, (core_radius _).trans sum_p1.2⟩
theorem core_p2 :
    lowLinearNumerator (Finset.Ico (11007) (11263)) (2) = 148594359927237214628835583711135959327661406155 ∧
    lowLinearRadius (Finset.Ico (11007) (11263)) (2) = 223134157702172448778909783202333861259 :=
  ⟨(core_center _).trans sum_p2.1, (core_radius _).trans sum_p2.2⟩
end KsIndex.AlphaRemarkTrial.Cache27392
