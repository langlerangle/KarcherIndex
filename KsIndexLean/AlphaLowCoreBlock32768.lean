module

public import KsIndexLean.AlphaLowModeSumAssembly
public import KsIndexLean.AlphaLowBlockCertificate32768

@[expose] public section

namespace KsIndex.AlphaRemarkTrial.Cache32768
theorem core_center (n : ℤ) :
    lowLinearNumerator (Finset.Ico (16383) (16385)) n =
      blockLinearNumerator (16383) n center := by
  apply (blockLinearNumerator_eq_core KsIndex.PositiveEnergyAlphaLowProd.valid
    (16383) n center ?_ ?_).symm
  · intro i
    convert low_block_covered 32768 2 (by norm_num) i using 1; norm_num
  · intro i
    simpa only [center, mode, show (-16385 : ℤ)+32768 = 16383 by norm_num] using (checked i).1

theorem core_radius (n : ℤ) :
    lowLinearRadius (Finset.Ico (16383) (16385)) n =
      blockLinearRadius (16383) n radius := by
  apply (blockLinearRadius_eq_core KsIndex.PositiveEnergyAlphaLowProd.valid
    (16383) n radius ?_ ?_).symm
  · intro i
    convert low_block_covered 32768 2 (by norm_num) i using 1; norm_num
  · intro i
    simpa only [radius, mode, show (-16385 : ℤ)+32768 = 16383 by norm_num] using (checked i).2
theorem core_m2 :
    lowLinearNumerator (Finset.Ico (16383) (16385)) (-2) = 656434477014201293226544946598163434620030393 ∧
    lowLinearRadius (Finset.Ico (16383) (16385)) (-2) = 964068236925990776247843794542252686 :=
  ⟨(core_center _).trans sum_m2.1, (core_radius _).trans sum_m2.2⟩
theorem core_m1 :
    lowLinearNumerator (Finset.Ico (16383) (16385)) (-1) = -656474540149906313142397899521581927414023201 ∧
    lowLinearRadius (Finset.Ico (16383) (16385)) (-1) = 964127075390391086621955813921501127 :=
  ⟨(core_center _).trans sum_m1.1, (core_radius _).trans sum_m1.2⟩
theorem core_p1 :
    lowLinearNumerator (Finset.Ico (16383) (16385)) (1) = -656554681093770421701639444327619495429298798 ∧
    lowLinearRadius (Finset.Ico (16383) (16385)) (1) = 964244773867796209791645911591985521 :=
  ⟨(core_center _).trans sum_p1.1, (core_radius _).trans sum_p1.2⟩
theorem core_p2 :
    lowLinearNumerator (Finset.Ico (16383) (16385)) (2) = 656594758903720800069100465620039605902187522 ∧
    lowLinearRadius (Finset.Ico (16383) (16385)) (2) = 964303633883431788622309373334265772 :=
  ⟨(core_center _).trans sum_p2.1, (core_radius _).trans sum_p2.2⟩
end KsIndex.AlphaRemarkTrial.Cache32768
