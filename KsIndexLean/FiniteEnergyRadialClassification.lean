module

public import KsIndexLean.WronskianEnergyExclusion
public import KsIndexLean.JacobiExtension

@[expose] public section


noncomputable section
open Set MeasureTheory
namespace KsIndex.Trace
open KsIndex.Radial KsIndex.JacobiExtension KsIndex.WeakH1

lemma finite_energy_eq_const_mul_uRad {k : ℕ} (hk : 2 ≤ k) (ℓ : ℕ)
    {f f' : ℝ → ℂ} (hfc : ContinuousOn f (Ioo (0 : ℝ) 1))
    (hf'c : ContinuousOn f' (Ioo (0 : ℝ) 1))
    (hf : ∀ r ∈ Ioo (0 : ℝ) 1, HasDerivAt f (f' r) r)
    (hode : ∀ r ∈ Ioo (0 : ℝ) 1, HasDerivAt (fun t : ℝ => (t : ℂ) * f' t)
      ((((ℓ : ℝ)^2 / r - r * Vrad k r : ℝ) : ℂ) * f r) r)
    (hE : ∃ B : ℝ, ∀ a : ℝ, 0 < a → a < 1 / 2 →
      (∫ r in Ioo a (1 / 2), r * ‖f' r‖ ^ 2 + r * ‖f r‖ ^ 2) ≤ B) :
    ∃ c : ℂ, ∀ r ∈ Ioo (0 : ℝ) 1, f r = c * (uRad k ℓ r : ℂ) := by
  let g : ℝ → ℂ := fun r => (uRad k ℓ r : ℂ)
  let g' : ℝ → ℂ := fun r => (uD k ℓ r : ℂ)
  have hg : ∀ r ∈ Ioo (0 : ℝ) 1, HasDerivAt g (g' r) r :=
    fun r hr => (uRad_hasDerivAt hk ℓ hr.1.ne').ofReal_comp
  have hG : ∀ r ∈ Ioo (0 : ℝ) 1, HasDerivAt (fun t : ℝ => (t : ℂ) * g' t)
      ((((ℓ : ℝ)^2 / r - r * Vrad k r : ℝ) : ℂ) * g r) r := by
    intro r hr
    have hd := (uRad_ode hk ℓ hr.1.ne').congr_deriv
      (show (ℓ : ℝ)^2 * uRad k ℓ r / r - r * Vrad k r * uRad k ℓ r =
        ((ℓ : ℝ)^2 / r - r * Vrad k r) * uRad k ℓ r by ring)
    simpa only [g, g', Complex.ofReal_mul] using hd.ofReal_comp
  have hgn : ∀ r ∈ Ioo (0 : ℝ) 1, g r ≠ 0 := by
    intro r hr
    have hp : 0 < uRad k ℓ r := mul_pos (pow_pos hr.1 _) (gRad_pos_Ioo hk ℓ hr)
    change (uRad k ℓ r : ℂ) ≠ 0
    exact_mod_cast hp.ne'
  obtain ⟨A, hA⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (uRad_continuousOn hk ℓ (Icc (0 : ℝ) 1))
  obtain ⟨D, hD⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (uD2_continuous hk ℓ).continuousOn (s := Icc (0 : ℝ) 1)
  let M := max (max A D) 0
  have hM : 0 ≤ M := le_max_right _ _
  have hgB : ∀ r ∈ Ioo (0 : ℝ) 1, ‖g r‖ ≤ M := by
    intro r hr
    have he : ‖g r‖ = ‖uRad k ℓ r‖ := Complex.norm_real _
    rw [he]
    exact (hA r (Ioo_subset_Icc_self hr)).trans ((le_max_left A D).trans (le_max_left _ _))
  have hg'B : ∀ r ∈ Ioo (0 : ℝ) 1, ‖g' r‖ ≤ M := by
    intro r hr
    have he : uD k ℓ r = uD2 k ℓ r :=
      (uRad_hasDerivAt hk ℓ hr.1.ne').unique (uRad_hasDerivAt' hk ℓ r)
    change ‖(uD k ℓ r : ℂ)‖ ≤ M
    rw [he, Complex.norm_real]
    exact (hD r (Ioo_subset_Icc_self hr)).trans ((le_max_right A D).trans (le_max_left _ _))
  have hW := radialWronskian_eq_const hf hg hode hG
  obtain ⟨B, hB⟩ := hE
  have hz := radialWronskian_eq_zero_of_energy hfc hf'c hM hgB hg'B hW hB
  exact eq_const_mul_of_radialWronskian_zero hf hg hgn (fun r hr => (hW r hr).trans hz)

/-- Actual weak disk modes are the explicit regular radial solutions. Finite
energy supplies the centre condition; no centre continuity is assumed. -/
lemma puncturedDiskMode_eq_const_mul_uRad {k : ℕ} (hk : 2 ≤ k)
    (u : ComplexH1) (n : ℤ)
    (hu : ∀ v : ComplexH1, v ∈ zeroTraceDomain Set.univ →
      weakJacobi (surfacePotential k) u v = 0) :
    ∃ c : ℂ, ∀ r ∈ Ioo (0 : ℝ) 1,
      puncturedDiskMode u n r = c * (uRad k n.natAbs r : ℂ) := by
  have hfc : ContinuousOn (puncturedDiskMode u n) (Ioo (0 : ℝ) 1) :=
    fun r hr => (puncturedDiskMode_hasDerivAt k u n hu hr).continuousAt.continuousWithinAt
  have hdc : ContinuousOn (puncturedDiskModeDerivative k u n) (Ioo (0 : ℝ) 1) := by
    intro r hr
    have ha : 0 < r / 2 := half_pos hr.1
    have hab : r / 2 < 1 := by linarith [hr.1, hr.2]
    exact ((puncturedDiskModeDerivative_continuousOn_annulus ha hab le_rfl k u n hu).continuousAt
      (Icc_mem_nhds (by linarith [hr.1]) hr.2)).continuousWithinAt
  apply finite_energy_eq_const_mul_uRad hk n.natAbs hfc hdc
    (fun r hr => puncturedDiskMode_hasDerivAt k u n hu hr)
  · intro r hr
    have hn : (n.natAbs : ℝ)^2 = (n : ℝ)^2 := by
      have hi : (n.natAbs : ℤ)^2 = n^2 := by rw [Int.natCast_natAbs, sq_abs]
      have hh := congrArg (fun z : ℤ => (z : ℝ)) hi
      simpa only [Int.cast_pow, Int.cast_natCast] using hh
    simpa only [Complex.real_smul, hn] using puncturedDiskMode_flux_hasDerivAt k u n hu hr
  · refine ⟨‖circleCoefficientCLM n‖ ^ 2 * (2 * (‖dxLp u‖ ^ 2 + ‖dyLp u‖ ^ 2)) +
      ‖circleCoefficientCLM n‖ ^ 2 * ‖valueCLM u‖ ^ 2, ?_⟩
    intro a ha hab
    have hD := puncturedDiskModeDerivative_continuousOn_annulus ha hab (by norm_num) k u n hu
    have hF := puncturedDiskMode_continuousOn_annulus ha hab (by norm_num) u n
    have hiD : IntegrableOn (fun r => r * ‖puncturedDiskModeDerivative k u n r‖ ^ 2)
        (Ioo a (1 / 2 : ℝ)) volume :=
      (continuousOn_id.mul (hD.norm.pow 2)).integrableOn_Icc.mono_set Ioo_subset_Icc_self
    have hiF : IntegrableOn (fun r => r * ‖puncturedDiskMode u n r‖ ^ 2)
        (Ioo a (1 / 2 : ℝ)) volume :=
      (continuousOn_id.mul (hF.norm.pow 2)).integrableOn_Icc.mono_set Ioo_subset_Icc_self
    rw [integral_add hiD hiF]
    exact add_le_add (puncturedDiskModeDerivative_weighted_energy_le ha hab (by norm_num) k u n hu)
      (puncturedDiskMode_weighted_energy_le ha hab (by norm_num) u n)

end KsIndex.Trace
