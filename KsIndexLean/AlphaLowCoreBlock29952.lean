module

public import KsIndexLean.AlphaLowModeSumAssembly
public import KsIndexLean.AlphaLowBlockCertificate29952

@[expose] public section

namespace KsIndex.AlphaRemarkTrial.Cache29952
theorem core_center (n : ℤ) :
    lowLinearNumerator (Finset.Ico (13567) (13823)) n =
      blockLinearNumerator (13567) n center := by
  apply (blockLinearNumerator_eq_core KsIndex.PositiveEnergyAlphaLowProd.valid
    (13567) n center ?_ ?_).symm
  · intro i
    convert low_block_covered 29952 256 (by norm_num) i using 1; norm_num
  · intro i
    simpa only [center, mode, show (-16385 : ℤ)+29952 = 13567 by norm_num] using (checked i).1

theorem core_radius (n : ℤ) :
    lowLinearRadius (Finset.Ico (13567) (13823)) n =
      blockLinearRadius (13567) n radius := by
  apply (blockLinearRadius_eq_core KsIndex.PositiveEnergyAlphaLowProd.valid
    (13567) n radius ?_ ?_).symm
  · intro i
    convert low_block_covered 29952 256 (by norm_num) i using 1; norm_num
  · intro i
    simpa only [radius, mode, show (-16385 : ℤ)+29952 = 13567 by norm_num] using (checked i).2
theorem core_m2 :
    lowLinearNumerator (Finset.Ico (13567) (13823)) (-2) = 109455663054761199808577425388398526075076072571 ∧
    lowLinearRadius (Finset.Ico (13567) (13823)) (-2) = 162418951504545940647591191088783386136 :=
  ⟨(core_center _).trans sum_m2.1, (core_radius _).trans sum_m2.2⟩
theorem core_m1 :
    lowLinearNumerator (Finset.Ico (13567) (13823)) (-1) = -109463655428531516251428805117887300817318488389 ∧
    lowLinearRadius (Finset.Ico (13567) (13823)) (-1) = 162430811239395864118190337701533088022 :=
  ⟨(core_center _).trans sum_m1.1, (core_radius _).trans sum_m1.2⟩
theorem core_p1 :
    lowLinearNumerator (Finset.Ico (13567) (13823)) (1) = -109479643678269880264992502016025769615874825397 ∧
    lowLinearRadius (Finset.Ico (13567) (13823)) (1) = 162454535905950517759335011974922738695 :=
  ⟨(core_center _).trans sum_p1.1, (core_radius _).trans sum_p1.2⟩
theorem core_p2 :
    lowLinearNumerator (Finset.Ico (13567) (13823)) (2) = 109487639554749525616235462175318790028005206880 ∧
    lowLinearRadius (Finset.Ico (13567) (13823)) (2) = 162466400838414400907988215216918491133 :=
  ⟨(core_center _).trans sum_p2.1, (core_radius _).trans sum_p2.2⟩
end KsIndex.AlphaRemarkTrial.Cache29952
