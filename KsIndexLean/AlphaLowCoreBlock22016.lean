module

public import KsIndexLean.AlphaLowModeSumAssembly
public import KsIndexLean.AlphaLowBlockCertificate22016

@[expose] public section

namespace KsIndex.AlphaRemarkTrial.Cache22016
theorem core_center (n : ℤ) :
    lowLinearNumerator (Finset.Ico (5631) (5887)) n =
      blockLinearNumerator (5631) n center := by
  apply (blockLinearNumerator_eq_core KsIndex.PositiveEnergyAlphaLowProd.valid
    (5631) n center ?_ ?_).symm
  · intro i
    convert low_block_covered 22016 256 (by norm_num) i using 1; norm_num
  · intro i
    simpa only [center, mode, show (-16385 : ℤ)+22016 = 5631 by norm_num] using (checked i).1

theorem core_radius (n : ℤ) :
    lowLinearRadius (Finset.Ico (5631) (5887)) n =
      blockLinearRadius (5631) n radius := by
  apply (blockLinearRadius_eq_core KsIndex.PositiveEnergyAlphaLowProd.valid
    (5631) n radius ?_ ?_).symm
  · intro i
    convert low_block_covered 22016 256 (by norm_num) i using 1; norm_num
  · intro i
    simpa only [radius, mode, show (-16385 : ℤ)+22016 = 5631 by norm_num] using (checked i).2
theorem core_m2 :
    lowLinearNumerator (Finset.Ico (5631) (5887)) (-2) = 393443486579484758765659306683054648554486841930 ∧
    lowLinearRadius (Finset.Ico (5631) (5887)) (-2) = 613530716441353358532809138167867555589 :=
  ⟨(core_center _).trans sum_m2.1, (core_radius _).trans sum_m2.2⟩
theorem core_m1 :
    lowLinearNumerator (Finset.Ico (5631) (5887)) (-1) = -393511820621236176989304998237750531741010354996 ∧
    lowLinearRadius (Finset.Ico (5631) (5887)) (-1) = 613637276667937231537974295662379474284 :=
  ⟨(core_center _).trans sum_m1.1, (core_radius _).trans sum_m1.2⟩
theorem core_p1 :
    lowLinearNumerator (Finset.Ico (5631) (5887)) (1) = -393648559951567470893013916860122630374095072978 ∧
    lowLinearRadius (Finset.Ico (5631) (5887)) (1) = 613850508224579141643237310656360539187 :=
  ⟨(core_center _).trans sum_p1.1, (core_radius _).trans sum_p1.2⟩
theorem core_p2 :
    lowLinearNumerator (Finset.Ico (5631) (5887)) (2) = 393716965264916988320329401357333570890226701405 ∧
    lowLinearRadius (Finset.Ico (5631) (5887)) (2) = 613957179593263727224052066354826287865 :=
  ⟨(core_center _).trans sum_p2.1, (core_radius _).trans sum_p2.2⟩
end KsIndex.AlphaRemarkTrial.Cache22016
