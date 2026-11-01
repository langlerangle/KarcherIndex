module

public import KsIndexLean.AlphaLowModeSumAssembly
public import KsIndexLean.AlphaLowBlockCertificate256

@[expose] public section

namespace KsIndex.AlphaRemarkTrial.Cache256
theorem core_center (n : ℤ) :
    lowLinearNumerator (Finset.Ico (-16129) (-15873)) n =
      blockLinearNumerator (-16129) n center := by
  apply (blockLinearNumerator_eq_core KsIndex.PositiveEnergyAlphaLowProd.valid
    (-16129) n center ?_ ?_).symm
  · intro i
    convert low_block_covered 256 256 (by norm_num) i using 1; norm_num
  · intro i
    simpa only [center, mode, show (-16385 : ℤ)+256 = -16129 by norm_num] using (checked i).1

theorem core_radius (n : ℤ) :
    lowLinearRadius (Finset.Ico (-16129) (-15873)) n =
      blockLinearRadius (-16129) n radius := by
  apply (blockLinearRadius_eq_core KsIndex.PositiveEnergyAlphaLowProd.valid
    (-16129) n radius ?_ ?_).symm
  · intro i
    convert low_block_covered 256 256 (by norm_num) i using 1; norm_num
  · intro i
    simpa only [radius, mode, show (-16385 : ℤ)+256 = -16129 by norm_num] using (checked i).2
theorem core_m2 :
    lowLinearNumerator (Finset.Ico (-16129) (-15873)) (-2) = -32759603564144513110607490749681906467375188362 ∧
    lowLinearRadius (Finset.Ico (-16129) (-15873)) (-2) = 127988985225523768038016464547759286556 :=
  ⟨(core_center _).trans sum_m2.1, (core_radius _).trans sum_m2.2⟩
theorem core_m1 :
    lowLinearNumerator (Finset.Ico (-16129) (-15873)) (-1) = 32757555987566308930517804116380030080029713283 ∧
    lowLinearRadius (Finset.Ico (-16129) (-15873)) (-1) = 127980985481816925537124984531785518295 :=
  ⟨(core_center _).trans sum_m1.1, (core_radius _).trans sum_m1.2⟩
theorem core_p1 :
    lowLinearNumerator (Finset.Ico (-16129) (-15873)) (1) = 32753461602209525414130335471856306883177911673 ∧
    lowLinearRadius (Finset.Ico (-16129) (-15873)) (1) = 127964988994158184361160970862208801310 :=
  ⟨(core_center _).trans sum_p1.1, (core_radius _).trans sum_p1.2⟩
theorem core_p2 :
    lowLinearNumerator (Finset.Ico (-16129) (-15873)) (2) = -32751414793334980274461935684610646823636512803 ∧
    lowLinearRadius (Finset.Ico (-16129) (-15873)) (2) = 127956992249831350372177683816477139834 :=
  ⟨(core_center _).trans sum_p2.1, (core_radius _).trans sum_p2.2⟩
end KsIndex.AlphaRemarkTrial.Cache256
