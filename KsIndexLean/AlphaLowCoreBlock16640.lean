module

public import KsIndexLean.AlphaLowModeSumAssembly
public import KsIndexLean.AlphaLowBlockCertificate16640

@[expose] public section

namespace KsIndex.AlphaRemarkTrial.Cache16640
theorem core_center (n : ℤ) :
    lowLinearNumerator (Finset.Ico (255) (511)) n =
      blockLinearNumerator (255) n center := by
  apply (blockLinearNumerator_eq_core KsIndex.PositiveEnergyAlphaLowProd.valid
    (255) n center ?_ ?_).symm
  · intro i
    convert low_block_covered 16640 256 (by norm_num) i using 1; norm_num
  · intro i
    simpa only [center, mode, show (-16385 : ℤ)+16640 = 255 by norm_num] using (checked i).1

theorem core_radius (n : ℤ) :
    lowLinearRadius (Finset.Ico (255) (511)) n =
      blockLinearRadius (255) n radius := by
  apply (blockLinearRadius_eq_core KsIndex.PositiveEnergyAlphaLowProd.valid
    (255) n radius ?_ ?_).symm
  · intro i
    convert low_block_covered 16640 256 (by norm_num) i using 1; norm_num
  · intro i
    simpa only [radius, mode, show (-16385 : ℤ)+16640 = 255 by norm_num] using (checked i).2
theorem core_m2 :
    lowLinearNumerator (Finset.Ico (255) (511)) (-2) = 23518923398818573690240900852955274358809367503256 ∧
    lowLinearRadius (Finset.Ico (255) (511)) (-2) = 42826684829587308160732517681518098192006 :=
  ⟨(core_center _).trans sum_m2.1, (core_radius _).trans sum_m2.2⟩
theorem core_m1 :
    lowLinearNumerator (Finset.Ico (255) (511)) (-1) = -23586483563820932107664818146872509011456128094769 ∧
    lowLinearRadius (Finset.Ico (255) (511)) (-1) = 42949968559751262173297895289031220419386 :=
  ⟨(core_center _).trans sum_m1.1, (core_radius _).trans sum_m1.2⟩
theorem core_p1 :
    lowLinearNumerator (Finset.Ico (255) (511)) (1) = -23722820790508231951071914487009784964288423855434 ∧
    lowLinearRadius (Finset.Ico (255) (511)) (1) = 43198761017279810946918158827666758711251 :=
  ⟨(core_center _).trans sum_p1.1, (core_radius _).trans sum_p1.2⟩
theorem core_p2 :
    lowLinearNumerator (Finset.Ico (255) (511)) (2) = 23791605443288113861350702339862559170521639502920 ∧
    lowLinearRadius (Finset.Ico (255) (511)) (2) = 43324283649061986214962188420748407302190 :=
  ⟨(core_center _).trans sum_p2.1, (core_radius _).trans sum_p2.2⟩
end KsIndex.AlphaRemarkTrial.Cache16640
