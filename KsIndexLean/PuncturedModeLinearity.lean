module

public import KsIndexLean.InteriorFourierReconstruction

@[expose] public section


noncomputable section
open Set MeasureTheory
namespace KsIndex.Trace
open KsIndex.WeakH1

lemma interiorDiskProfile_smul_ae {a b : ℝ} (ha : 0 < a) (hb : b ≤ 1)
    (c : ℂ) (u : ComplexH1) :
    interiorDiskProfile a b (c • u) =ᵐ[volume.restrict (Ioo a b)]
      c • interiorDiskProfile a b u := by
  have hc := (Lp.coeFn_smul c (valueCLM u)).filter_mono
    (ae_mono (Measure.restrict_mono (interiorAnnulus_subset_disk (a := a) hb) le_rfl))
  dsimp [interiorDiskProfile]
  rw [map_smul]
  filter_upwards [sliceLp_congr_ae ha hc,
    sliceLp_smul_ae ha c (interiorAnnulus_memLp hb (valueCLM u))] with r hr hs
  exact hr.trans hs

lemma interiorDiskRepresentative_smul {a b : ℝ}
    (ha : 0 < a) (hab : a < b) (hb : b ≤ 1) (c : ℂ) (u : ComplexH1)
    {r : ℝ} (hr : r ∈ Icc a b) :
    interiorDiskRepresentative hab (c • u) r = c • interiorDiskRepresentative hab u r := by
  apply eqOn_Icc_of_ae_eq hab
    (interiorDiskRepresentative_continuousOn ha hab hb (c • u))
    ((interiorDiskRepresentative_continuousOn ha hab hb u).const_smul c) ?_ hr
  filter_upwards [interiorDiskRepresentative_ae ha hab hb (c • u),
    interiorDiskRepresentative_ae ha hab hb u, interiorDiskProfile_smul_ae ha hb c u]
    with t hs hu he
  exact hs.symm.trans (he.trans (congrArg (fun x => c • x) hu))

lemma puncturedDiskMode_smul (c : ℂ) (u : ComplexH1) (n : ℤ)
    {r : ℝ} (hr : r ∈ Ioc (0 : ℝ) 1) :
    puncturedDiskMode (c • u) n r = c * puncturedDiskMode u n r := by
  have hab : r / 2 < 1 := by linarith [hr.1, hr.2]
  have hri : r ∈ Icc (r / 2) 1 := ⟨by linarith [hr.1], hr.2⟩
  rw [puncturedDiskMode_eq_interior (half_pos hr.1) hab le_rfl (c • u) n hri,
    puncturedDiskMode_eq_interior (half_pos hr.1) hab le_rfl u n hri]
  unfold interiorDiskMode
  rw [interiorDiskRepresentative_smul (half_pos hr.1) hab le_rfl c u hri, map_smul]
  rfl

lemma puncturedDiskMode_zero (n : ℤ) {r : ℝ} (hr : r ∈ Ioc (0 : ℝ) 1) :
    puncturedDiskMode 0 n r = 0 := by
  have h := puncturedDiskMode_smul 0 (0 : ComplexH1) n hr
  simpa using h

end KsIndex.Trace
