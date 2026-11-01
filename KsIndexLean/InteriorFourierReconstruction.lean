module

public import KsIndexLean.WeakDirichletModeSelection

@[expose] public section


noncomputable section
open Set MeasureTheory
namespace KsIndex.Trace
open KsIndex.WeakH1

/-- Completeness of the circle Fourier system for the coefficient CLMs. -/
lemma circle_eq_of_coefficients_eq {f g : Lp ℂ 2 circleMeasure}
    (h : ∀ n : ℤ, circleCoefficientCLM n f = circleCoefficientCLM n g) : f = g := by
  apply circleFourierCLE.injective
  apply Subtype.ext
  funext n
  simpa only [circleFourierCLE_apply, circleCoefficientCLM_apply] using h n

/-- All angular modes determine the continuous circle profile. -/
lemma interiorDiskRepresentative_eq_of_modes {a b : ℝ} (hab : a < b)
    (u v : ComplexH1) (r : ℝ)
    (h : ∀ n : ℤ, interiorDiskMode hab u n r = interiorDiskMode hab v n r) :
    interiorDiskRepresentative hab u r = interiorDiskRepresentative hab v r :=
  circle_eq_of_coefficients_eq h

/-- Punctured modes determine the annular slice profiles almost everywhere.
No weak equation or boundary hypothesis is required. -/
lemma interiorDiskProfile_ae_eq_of_punctured_modes {a b : ℝ}
    (ha : 0 < a) (hab : a < b) (hb : b ≤ 1) (u v : ComplexH1)
    (h : ∀ n : ℤ, ∀ r ∈ Ioc (0 : ℝ) 1,
      puncturedDiskMode u n r = puncturedDiskMode v n r) :
    interiorDiskProfile a b u =ᵐ[volume.restrict (Ioo a b)] interiorDiskProfile a b v := by
  filter_upwards [interiorDiskRepresentative_ae ha hab hb u,
    interiorDiskRepresentative_ae ha hab hb v, ae_restrict_mem measurableSet_Ioo] with r hu hv hr
  rw [hu, hv]
  apply interiorDiskRepresentative_eq_of_modes
  intro n
  have hr' : r ∈ Icc a b := Ioo_subset_Icc_self hr
  rw [← puncturedDiskMode_eq_interior ha hab hb u n hr',
    ← puncturedDiskMode_eq_interior ha hab hb v n hr']
  exact h n r ⟨ha.trans hr.1, hr.2.le.trans hb⟩

/-- Vanishing slice profiles force vanishing of the original annular function. -/
lemma ae_zero_of_sliceLp_zero {a b : ℝ} (ha : 0 < a) {f : ℂ → ℂ}
    (hf : MemLp f 2 (volume.restrict (annulusSet a b)))
    (hs : sliceLp a b f =ᵐ[volume.restrict (Ioo a b)] 0) :
    f =ᵐ[volume.restrict (annulusSet a b)] 0 := by
  have hi : (∫⁻ z in annulusSet a b, ‖f z‖ₑ ^ (2 : ℕ)) = 0 := by
    rw [lintegral_annulus_eq_weighted_sliceLp ha hf]
    have hz : (fun r => ENNReal.ofReal r * ‖sliceLp a b f r‖ₑ ^ (2 : ℕ))
        =ᵐ[volume.restrict (Ioo a b)] 0 := by
      filter_upwards [hs] with r hr
      simp [hr]
    rw [lintegral_congr_ae hz]
    simp
  have hz := (lintegral_eq_zero_iff' (hf.aestronglyMeasurable.enorm.pow_const 2)).mp hi
  filter_upwards [hz] with z hz
  simpa using hz

/-- Equality of annular slice profiles implies equality of the underlying functions. -/
lemma ae_eq_of_sliceLp_eq {a b : ℝ} (ha : 0 < a) {f g : ℂ → ℂ}
    (hf : MemLp f 2 (volume.restrict (annulusSet a b)))
    (hg : MemLp g 2 (volume.restrict (annulusSet a b)))
    (hs : sliceLp a b f =ᵐ[volume.restrict (Ioo a b)] sliceLp a b g) :
    f =ᵐ[volume.restrict (annulusSet a b)] g := by
  have hd : sliceLp a b (f - g) =ᵐ[volume.restrict (Ioo a b)] 0 := by
    filter_upwards [ae_sliceFun_memLp ha hf, ae_sliceFun_memLp ha hg,
      ae_restrict_mem measurableSet_Ioo, hs] with r hfr hgr hr he
    rw [sliceLp_of_memLp (u := f - g) hr (hfr.sub hgr)]
    apply Lp.ext
    have he' : hfr.toLp (sliceFun f r) = hgr.toLp (sliceFun g r) := by
      simpa only [sliceLp_of_memLp hr hfr, sliceLp_of_memLp hr hgr] using he
    have hraw := hfr.coeFn_toLp.symm.trans ((congrArg (fun q : Lp ℂ 2 circleMeasure =>
      (q : Circle → ℂ)) he').eventuallyEq.trans hgr.coeFn_toLp)
    filter_upwards [(hfr.sub hgr).coeFn_toLp, hraw,
      Lp.coeFn_zero ℂ 2 circleMeasure] with w hw hew hz
    change (hfr.sub hgr).toLp (sliceFun f r - sliceFun g r) w = (0 : Lp ℂ 2 circleMeasure) w
    rw [hw, hz]
    exact sub_eq_zero.mpr hew
  have hz := ae_zero_of_sliceLp_zero ha (hf.sub hg) hd
  filter_upwards [hz] with z hz
  exact sub_eq_zero.mp hz

/-- The complete punctured Fourier data determines the weak disk function. -/
lemma complexH1_eq_of_punctured_modes (u v : ComplexH1)
    (h : ∀ n : ℤ, ∀ r ∈ Ioc (0 : ℝ) 1,
      puncturedDiskMode u n r = puncturedDiskMode v n r) : u = v := by
  have ha (q : ℚ) (hq : 0 < (q : ℝ)) (hq1 : (q : ℝ) < 1) :
      (valueCLM u : ℂ → ℂ) =ᵐ[volume.restrict (annulusSet (q : ℝ) 1)] valueCLM v :=
    ae_eq_of_sliceLp_eq hq (interiorAnnulus_memLp le_rfl (valueCLM u))
      (interiorAnnulus_memLp le_rfl (valueCLM v))
      (interiorDiskProfile_ae_eq_of_punctured_modes hq hq1 le_rfl u v h)
  have hall : ∀ᵐ z ∂(volume : Measure ℂ), ∀ q : ℚ,
      0 < (q : ℝ) → (q : ℝ) < 1 → z ∈ annulusSet (q : ℝ) 1 →
      valueCLM u z = valueCLM v z := by
    rw [ae_all_iff]
    intro q
    by_cases hq : 0 < (q : ℝ)
    · by_cases hq1 : (q : ℝ) < 1
      · filter_upwards [(ae_restrict_iff' measurableSet_annulusSet).mp (ha q hq hq1)] with z hz
        exact fun _ _ => hz
      · exact Filter.Eventually.of_forall fun _ _ hh => (hq1 hh).elim
    · exact Filter.Eventually.of_forall fun _ hh => (hq hh).elim
  apply valueCLM_injective
  apply Lp.ext
  apply (ae_restrict_iff' measurableSet_ball).mpr
  filter_upwards [hall, volume.ae_ne (0 : ℂ)] with z hz hz0 hzd
  have hnorm : 0 < ‖z‖ := norm_pos_iff.mpr hz0
  obtain ⟨q, hq, hqz⟩ := exists_rat_btwn hnorm
  have hz1 : ‖z‖ < 1 := by simpa [disk, Metric.mem_ball, dist_zero_right] using hzd
  exact hz q hq (hqz.trans hz1) ⟨hqz, hz1⟩

end KsIndex.Trace
