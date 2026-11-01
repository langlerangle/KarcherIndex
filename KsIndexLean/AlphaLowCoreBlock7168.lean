module

public import KsIndexLean.AlphaLowModeSumAssembly
public import KsIndexLean.AlphaLowBlockCertificate7168

@[expose] public section

namespace KsIndex.AlphaRemarkTrial.Cache7168
theorem core_center (n : ℤ) :
    lowLinearNumerator (Finset.Ico (-9217) (-8961)) n =
      blockLinearNumerator (-9217) n center := by
  apply (blockLinearNumerator_eq_core KsIndex.PositiveEnergyAlphaLowProd.valid
    (-9217) n center ?_ ?_).symm
  · intro i
    convert low_block_covered 7168 256 (by norm_num) i using 1; norm_num
  · intro i
    simpa only [center, mode, show (-16385 : ℤ)+7168 = -9217 by norm_num] using (checked i).1

theorem core_radius (n : ℤ) :
    lowLinearRadius (Finset.Ico (-9217) (-8961)) n =
      blockLinearRadius (-9217) n radius := by
  apply (blockLinearRadius_eq_core KsIndex.PositiveEnergyAlphaLowProd.valid
    (-9217) n radius ?_ ?_).symm
  · intro i
    convert low_block_covered 7168 256 (by norm_num) i using 1; norm_num
  · intro i
    simpa only [radius, mode, show (-16385 : ℤ)+7168 = -9217 by norm_num] using (checked i).2
theorem core_m2 :
    lowLinearNumerator (Finset.Ico (-9217) (-8961)) (-2) = -68809179679232743992551994937140672088790235501 ∧
    lowLinearRadius (Finset.Ico (-9217) (-8961)) (-2) = 304664529947852916001018247157707346971 :=
  ⟨(core_center _).trans sum_m2.1, (core_radius _).trans sum_m2.2⟩
theorem core_m1 :
    lowLinearNumerator (Finset.Ico (-9217) (-8961)) (-1) = 68801607093446102754486625763731682690261560029 ∧
    lowLinearRadius (Finset.Ico (-9217) (-8961)) (-1) = 304631000503509361399774357740057186421 :=
  ⟨(core_center _).trans sum_m1.1, (core_radius _).trans sum_m1.2⟩
theorem core_p1 :
    lowLinearNumerator (Finset.Ico (-9217) (-8961)) (1) = 68786466921370839081842474559185207663541947705 ∧
    lowLinearRadius (Finset.Ico (-9217) (-8961)) (1) = 304563963751640137538547695101953503420 :=
  ⟨(core_center _).trans sum_p1.1, (core_radius _).trans sum_p1.2⟩
theorem core_p2 :
    lowLinearNumerator (Finset.Ico (-9217) (-8961)) (2) = -68778899333982025223529095752735146839876112030 ∧
    lowLinearRadius (Finset.Ico (-9217) (-8961)) (2) = 304530456439242957338890353397443709895 :=
  ⟨(core_center _).trans sum_p2.1, (core_radius _).trans sum_p2.2⟩
end KsIndex.AlphaRemarkTrial.Cache7168
