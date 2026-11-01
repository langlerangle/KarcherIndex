module

public import KsIndexLean.AlphaLowModeSumAssembly
public import KsIndexLean.AlphaLowBlockCertificate16128

@[expose] public section

namespace KsIndex.AlphaRemarkTrial.Cache16128
theorem core_center (n : ℤ) :
    lowLinearNumerator (Finset.Ico (-257) (-1)) n =
      blockLinearNumerator (-257) n center := by
  apply (blockLinearNumerator_eq_core KsIndex.PositiveEnergyAlphaLowProd.valid
    (-257) n center ?_ ?_).symm
  · intro i
    convert low_block_covered 16128 256 (by norm_num) i using 1; norm_num
  · intro i
    simpa only [center, mode, show (-16385 : ℤ)+16128 = -257 by norm_num] using (checked i).1

theorem core_radius (n : ℤ) :
    lowLinearRadius (Finset.Ico (-257) (-1)) n =
      blockLinearRadius (-257) n radius := by
  apply (blockLinearRadius_eq_core KsIndex.PositiveEnergyAlphaLowProd.valid
    (-257) n radius ?_ ?_).symm
  · intro i
    convert low_block_covered 16128 256 (by norm_num) i using 1; norm_num
  · intro i
    simpa only [radius, mode, show (-16385 : ℤ)+16128 = -257 by norm_num] using (checked i).2
theorem core_m2 :
    lowLinearNumerator (Finset.Ico (-257) (-1)) (-2) = 39210950986984049390386864419033718213746990579396 ∧
    lowLinearRadius (Finset.Ico (-257) (-1)) (-2) = 13463279338109724388128814291043915581285663 :=
  ⟨(core_center _).trans sum_m2.1, (core_radius _).trans sum_m2.2⟩
theorem core_m1 :
    lowLinearNumerator (Finset.Ico (-257) (-1)) (-1) = -287717516109902807296565405457588435013185830286749 ∧
    lowLinearRadius (Finset.Ico (-257) (-1)) (-1) = 10218692333315751868358669089843859205979360 :=
  ⟨(core_center _).trans sum_m1.1, (core_radius _).trans sum_m1.2⟩
theorem core_p1 :
    lowLinearNumerator (Finset.Ico (-257) (-1)) (1) = -96620808461405080634353728579922041456395854298792 ∧
    lowLinearRadius (Finset.Ico (-257) (-1)) (1) = 3337405840435336338621884857563501401741849 :=
  ⟨(core_center _).trans sum_p1.1, (core_radius _).trans sum_p1.2⟩
theorem core_p2 :
    lowLinearNumerator (Finset.Ico (-257) (-1)) (2) = 76278021443642806245395161098417822839096742217351 ∧
    lowLinearRadius (Finset.Ico (-257) (-1)) (2) = 2678662526964894704368210932120727992629819 :=
  ⟨(core_center _).trans sum_p2.1, (core_radius _).trans sum_p2.2⟩
end KsIndex.AlphaRemarkTrial.Cache16128
