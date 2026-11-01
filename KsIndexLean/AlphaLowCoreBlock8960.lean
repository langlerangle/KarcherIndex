module

public import KsIndexLean.AlphaLowModeSumAssembly
public import KsIndexLean.AlphaLowBlockCertificate8960

@[expose] public section

namespace KsIndex.AlphaRemarkTrial.Cache8960
theorem core_center (n : ℤ) :
    lowLinearNumerator (Finset.Ico (-7425) (-7169)) n =
      blockLinearNumerator (-7425) n center := by
  apply (blockLinearNumerator_eq_core KsIndex.PositiveEnergyAlphaLowProd.valid
    (-7425) n center ?_ ?_).symm
  · intro i
    convert low_block_covered 8960 256 (by norm_num) i using 1; norm_num
  · intro i
    simpa only [center, mode, show (-16385 : ℤ)+8960 = -7425 by norm_num] using (checked i).1

theorem core_radius (n : ℤ) :
    lowLinearRadius (Finset.Ico (-7425) (-7169)) n =
      blockLinearRadius (-7425) n radius := by
  apply (blockLinearRadius_eq_core KsIndex.PositiveEnergyAlphaLowProd.valid
    (-7425) n radius ?_ ?_).symm
  · intro i
    convert low_block_covered 8960 256 (by norm_num) i using 1; norm_num
  · intro i
    simpa only [radius, mode, show (-16385 : ℤ)+8960 = -7425 by norm_num] using (checked i).2
theorem core_m2 :
    lowLinearNumerator (Finset.Ico (-7425) (-7169)) (-2) = -91532873353856276220993231328302809032203854402 ∧
    lowLinearRadius (Finset.Ico (-7425) (-7169)) (-2) = 426792022664277863582581825255530312983 :=
  ⟨(core_center _).trans sum_m2.1, (core_radius _).trans sum_m2.2⟩
theorem core_m1 :
    lowLinearNumerator (Finset.Ico (-7425) (-7169)) (-1) = 91520324774946329923280003584787027451644898653 ∧
    lowLinearRadius (Finset.Ico (-7425) (-7169)) (-1) = 426733510733478997322979502426692846706 :=
  ⟨(core_center _).trans sum_m1.1, (core_radius _).trans sum_m1.2⟩
theorem core_p1 :
    lowLinearNumerator (Finset.Ico (-7425) (-7169)) (1) = 91495237937340857277724198640632948314363575382 ∧
    lowLinearRadius (Finset.Ico (-7425) (-7169)) (1) = 426616534994503578950940355534140151653 :=
  ⟨(core_center _).trans sum_p1.1, (core_radius _).trans sum_p1.2⟩
theorem core_p2 :
    lowLinearNumerator (Finset.Ico (-7425) (-7169)) (2) = -91482699675816241804709806460859668825471142091 ∧
    lowLinearRadius (Finset.Ico (-7425) (-7169)) (2) = 426558071173134807291612860870080083485 :=
  ⟨(core_center _).trans sum_p2.1, (core_radius _).trans sum_p2.2⟩
end KsIndex.AlphaRemarkTrial.Cache8960
