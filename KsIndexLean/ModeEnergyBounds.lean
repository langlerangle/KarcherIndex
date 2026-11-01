module

public import KsIndexLean.PuncturedDiskModes

@[expose] public section


noncomputable section
open Set MeasureTheory
namespace KsIndex.Trace
open KsIndex.WeakH1

lemma coefficient_weighted_energy_le {a b : ℝ} (ha : 0 < a) (hab : a < b)
    {f : ℂ → ℂ} (hf : MemLp f 2 (volume.restrict (annulusSet a b))) (n : ℤ) :
    (∫ r in Ioo a b, r * ‖circleCoefficientCLM n (sliceLp a b f r)‖ ^ 2) ≤
      ‖circleCoefficientCLM n‖ ^ 2 * ∫ z in annulusSet a b, ‖f z‖ ^ 2 := by
  have hs := intervalIntegrable_sliceLp_norm_sq ha hab hf
  have hw : IntervalIntegrable (fun r => r * ‖sliceLp a b f r‖ ^ 2) volume a b :=
    hs.continuousOn_smul continuous_id.continuousOn
  have hi := ((intervalIntegrable_iff_integrableOn_Ioo_of_le hab.le).mp hw).const_mul
    (‖circleCoefficientCLM n‖ ^ 2)
  have hpoint : ∀ᵐ r ∂volume.restrict (Ioo a b),
      r * ‖circleCoefficientCLM n (sliceLp a b f r)‖ ^ 2 ≤
        ‖circleCoefficientCLM n‖ ^ 2 * (r * ‖sliceLp a b f r‖ ^ 2) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with r hr
    have hnorm := (circleCoefficientCLM n).le_opNorm (sliceLp a b f r)
    have hsq := (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))).mpr hnorm
    have h := mul_le_mul_of_nonneg_left hsq (ha.trans hr.1).le
    nlinarith
  have hm := (circleCoefficientCLM n).continuous.comp_aestronglyMeasurable
    (aestronglyMeasurable_sliceLp ha hf)
  have hlow : IntegrableOn (fun r => r * ‖circleCoefficientCLM n (sliceLp a b f r)‖ ^ 2)
      (Ioo a b) volume := by
    apply hi.mono' (aestronglyMeasurable_id.mul (hm.norm.pow 2))
    filter_upwards [hpoint, ae_restrict_mem measurableSet_Ioo] with r hr hrI
    simpa only [Pi.mul_apply, Pi.pow_apply, id_eq, Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (ha.trans hrI.1).le (sq_nonneg _))] using hr
  calc _ ≤ ∫ r in Ioo a b, ‖circleCoefficientCLM n‖ ^ 2 * (r * ‖sliceLp a b f r‖ ^ 2) :=
      integral_mono_ae hlow hi hpoint
    _ = _ := by rw [integral_const_mul, ← integral_annulus_eq_weighted_sliceLp ha hf]

lemma interiorAnnulus_energy_le {a b : ℝ} (hb : b ≤ 1) (f : L2C) :
    (∫ z in annulusSet a b, ‖f z‖ ^ 2) ≤ ‖f‖ ^ 2 := by
  rw [lp_norm_sq]
  exact setIntegral_mono_set
    ((memLp_two_iff_integrable_sq_norm (Lp.memLp f).aestronglyMeasurable).mp (Lp.memLp f))
    (Filter.Eventually.of_forall (fun z => sq_nonneg _))
    (Filter.Eventually.of_forall (interiorAnnulus_subset_disk hb))

lemma puncturedDiskMode_weighted_energy_le {a b : ℝ}
    (ha : 0 < a) (hab : a < b) (hb : b ≤ 1) (u : ComplexH1) (n : ℤ) :
    (∫ r in Ioo a b, r * ‖puncturedDiskMode u n r‖ ^ 2) ≤
      ‖circleCoefficientCLM n‖ ^ 2 * ‖valueCLM u‖ ^ 2 := by
  have he : (∫ r in Ioo a b, r * ‖puncturedDiskMode u n r‖ ^ 2) =
      ∫ r in Ioo a b, r * ‖circleCoefficientCLM n (sliceLp a b (valueCLM u) r)‖ ^ 2 := by
    apply integral_congr_ae
    filter_upwards [interiorDiskRepresentative_ae ha hab hb u,
      ae_restrict_mem measurableSet_Ioo] with r hr hrI
    rw [puncturedDiskMode_eq_interior ha hab hb u n (Ioo_subset_Icc_self hrI)]
    change r * ‖circleCoefficientCLM n (interiorDiskRepresentative hab u r)‖ ^ 2 = _
    rw [← hr]
    rfl
  rw [he]
  exact (coefficient_weighted_energy_le ha hab (interiorAnnulus_memLp (a := a) hb (valueCLM u)) n).trans
    (mul_le_mul_of_nonneg_left (interiorAnnulus_energy_le hb (valueCLM u)) (sq_nonneg _))

lemma puncturedDiskModeDerivative_weighted_energy_le {a b : ℝ}
    (ha : 0 < a) (hab : a < b) (hb : b ≤ 1) (k : ℕ) (u : ComplexH1) (n : ℤ)
    (hu : ∀ v : ComplexH1, v ∈ zeroTraceDomain Set.univ →
      weakJacobi (surfacePotential k) u v = 0) :
    (∫ r in Ioo a b, r * ‖puncturedDiskModeDerivative k u n r‖ ^ 2) ≤
      ‖circleCoefficientCLM n‖ ^ 2 * (2 * (‖dxLp u‖ ^ 2 + ‖dyLp u‖ ^ 2)) := by
  have h1 : MemLp (fun z => Dxy (dxLp u) (dyLp u) z 1) 2
      (volume.restrict (annulusSet a b)) := by simpa using interiorAnnulus_memLp (a := a) hb (dxLp u)
  have hI : MemLp (fun z => Dxy (dxLp u) (dyLp u) z Complex.I) 2
      (volume.restrict (annulusSet a b)) := by simpa using interiorAnnulus_memLp (a := a) hb (dyLp u)
  have hm := memLp_radialField ha h1 hI
  have he : (∫ r in Ioo a b, r * ‖puncturedDiskModeDerivative k u n r‖ ^ 2) =
      ∫ r in Ioo a b, r * ‖circleCoefficientCLM n
        (sliceLp a b (radialField (Dxy (dxLp u) (dyLp u))) r)‖ ^ 2 := by
    apply integral_congr_ae
    filter_upwards [interiorDiskClassicalDerivative_ae ha hab hb k u n hu,
      ae_restrict_mem measurableSet_Ioo] with r hr hrI
    rw [puncturedDiskModeDerivative_eq_interior ha hab hb k u n hu (Ioo_subset_Icc_self hrI), ← hr]
    rfl
  rw [he]
  apply (coefficient_weighted_energy_le ha hab hm n).trans
  apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
  have h := integral_radialField_le ha h1 hI
  simp only [Dxy_one, Dxy_I] at h
  have hx := (memLp_two_iff_integrable_sq_norm (interiorAnnulus_memLp (a := a) hb (dxLp u)).aestronglyMeasurable).mp
    (interiorAnnulus_memLp (a := a) hb (dxLp u))
  have hy := (memLp_two_iff_integrable_sq_norm (interiorAnnulus_memLp (a := a) hb (dyLp u)).aestronglyMeasurable).mp
    (interiorAnnulus_memLp (a := a) hb (dyLp u))
  rw [integral_add hx hy] at h
  exact h.trans (mul_le_mul_of_nonneg_left
    (add_le_add (interiorAnnulus_energy_le hb (dxLp u)) (interiorAnnulus_energy_le hb (dyLp u)))
    (by norm_num))

end KsIndex.Trace
