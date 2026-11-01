module

public import KsIndexLean.AlphaLowModeSumAssembly
public import KsIndexLean.AlphaLowBlockCertificate11520

@[expose] public section

namespace KsIndex.AlphaRemarkTrial.Cache11520
theorem core_center (n : ℤ) :
    lowLinearNumerator (Finset.Ico (-4865) (-4609)) n =
      blockLinearNumerator (-4865) n center := by
  apply (blockLinearNumerator_eq_core KsIndex.PositiveEnergyAlphaLowProd.valid
    (-4865) n center ?_ ?_).symm
  · intro i
    convert low_block_covered 11520 256 (by norm_num) i using 1; norm_num
  · intro i
    simpa only [center, mode, show (-16385 : ℤ)+11520 = -4865 by norm_num] using (checked i).1

theorem core_radius (n : ℤ) :
    lowLinearRadius (Finset.Ico (-4865) (-4609)) n =
      blockLinearRadius (-4865) n radius := by
  apply (blockLinearRadius_eq_core KsIndex.PositiveEnergyAlphaLowProd.valid
    (-4865) n radius ?_ ?_).symm
  · intro i
    convert low_block_covered 11520 256 (by norm_num) i using 1; norm_num
  · intro i
    simpa only [radius, mode, show (-16385 : ℤ)+11520 = -4865 by norm_num] using (checked i).2
theorem core_m2 :
    lowLinearNumerator (Finset.Ico (-4865) (-4609)) (-2) = -159625147533711683875368020572734333839924675652 ∧
    lowLinearRadius (Finset.Ico (-4865) (-4609)) (-2) = 828939271175633675786204701550032528973 :=
  ⟨(core_center _).trans sum_m2.1, (core_radius _).trans sum_m2.2⟩
theorem core_m1 :
    lowLinearNumerator (Finset.Ico (-4865) (-4609)) (-1) = 159591424198018580223683545431328251898215119605 ∧
    lowLinearRadius (Finset.Ico (-4865) (-4609)) (-1) = 828764133604394257900116598758102585572 :=
  ⟨(core_center _).trans sum_m1.1, (core_radius _).trans sum_m1.2⟩
theorem core_p1 :
    lowLinearNumerator (Finset.Ico (-4865) (-4609)) (1) = 159524020266502969064888853637112477875126122179 ∧
    lowLinearRadius (Finset.Ico (-4865) (-4609)) (1) = 828414080439627839884319187584795961863 :=
  ⟨(core_center _).trans sum_p1.1, (core_radius _).trans sum_p1.2⟩
theorem core_p2 :
    lowLinearNumerator (Finset.Ico (-4865) (-4609)) (2) = -159490339652624173365745621870865593125261995035 ∧
    lowLinearRadius (Finset.Ico (-4865) (-4609)) (2) = 828239164752316139793206751108704299296 :=
  ⟨(core_center _).trans sum_p2.1, (core_radius _).trans sum_p2.2⟩
end KsIndex.AlphaRemarkTrial.Cache11520
