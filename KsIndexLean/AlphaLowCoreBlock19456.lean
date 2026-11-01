module

public import KsIndexLean.AlphaLowModeSumAssembly
public import KsIndexLean.AlphaLowBlockCertificate19456

@[expose] public section

namespace KsIndex.AlphaRemarkTrial.Cache19456
theorem core_center (n : ℤ) :
    lowLinearNumerator (Finset.Ico (3071) (3327)) n =
      blockLinearNumerator (3071) n center := by
  apply (blockLinearNumerator_eq_core KsIndex.PositiveEnergyAlphaLowProd.valid
    (3071) n center ?_ ?_).symm
  · intro i
    convert low_block_covered 19456 256 (by norm_num) i using 1; norm_num
  · intro i
    simpa only [center, mode, show (-16385 : ℤ)+19456 = 3071 by norm_num] using (checked i).1

theorem core_radius (n : ℤ) :
    lowLinearRadius (Finset.Ico (3071) (3327)) n =
      blockLinearRadius (3071) n radius := by
  apply (blockLinearRadius_eq_core KsIndex.PositiveEnergyAlphaLowProd.valid
    (3071) n radius ?_ ?_).symm
  · intro i
    convert low_block_covered 19456 256 (by norm_num) i using 1; norm_num
  · intro i
    simpa only [radius, mode, show (-16385 : ℤ)+19456 = 3071 by norm_num] using (checked i).2
theorem core_m2 :
    lowLinearNumerator (Finset.Ico (3071) (3327)) (-2) = 939528500130250565463533976970944500819507045166 ∧
    lowLinearRadius (Finset.Ico (3071) (3327)) (-2) = 1514859531729821332247405322802564976026 :=
  ⟨(core_center _).trans sum_m2.1, (core_radius _).trans sum_m2.2⟩
theorem core_m1 :
    lowLinearNumerator (Finset.Ico (3071) (3327)) (-1) = -939822491851108094580171130554149855779274346557 ∧
    lowLinearRadius (Finset.Ico (3071) (3327)) (-1) = 1515333566941382595772631357455501909731 :=
  ⟨(core_center _).trans sum_m1.1, (core_radius _).trans sum_m1.2⟩
theorem core_p1 :
    lowLinearNumerator (Finset.Ico (3071) (3327)) (1) = -940411027898515189481001917653228692040412571454 ∧
    lowLinearRadius (Finset.Ico (3071) (3327)) (1) = 1516282528418350080238619610487783988529 :=
  ⟨(core_center _).trans sum_p1.1, (core_radius _).trans sum_p1.2⟩
theorem core_p2 :
    lowLinearNumerator (Finset.Ico (3071) (3327)) (2) = 940705572571595891635912188118158516504014059312 ∧
    lowLinearRadius (Finset.Ico (3071) (3327)) (2) = 1516757455242540263311502344390230125077 :=
  ⟨(core_center _).trans sum_p2.1, (core_radius _).trans sum_p2.2⟩
end KsIndex.AlphaRemarkTrial.Cache19456
