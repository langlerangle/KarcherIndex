module

public import KsIndexLean.FiniteEnergyRadialClassification

@[expose] public section


noncomputable section
open Set MeasureTheory
namespace KsIndex.Trace
open KsIndex.WeakH1 KsIndex.Radial

lemma puncturedDiskMode_eq_const_mul_uRad_closed {k : ℕ} (hk : 2 ≤ k)
    (u : ComplexH1) (n : ℤ)
    (hu : ∀ v : ComplexH1, v ∈ zeroTraceDomain Set.univ →
      weakJacobi (surfacePotential k) u v = 0) :
    ∃ c : ℂ, ∀ r ∈ Ioc (0 : ℝ) 1,
      puncturedDiskMode u n r = c * (uRad k n.natAbs r : ℂ) := by
  obtain ⟨c, hc⟩ := puncturedDiskMode_eq_const_mul_uRad hk u n hu
  have he : EqOn (puncturedDiskMode u n) (fun r => c * (uRad k n.natAbs r : ℂ))
      (Icc (1 / 2 : ℝ) 1) := by
    apply Set.EqOn.of_subset_closure (s := Ioo (1 / 2 : ℝ) 1)
      (fun r hr => hc r ⟨by linarith [hr.1], hr.2⟩)
      (puncturedDiskMode_continuousOn_annulus (by norm_num) (by norm_num) le_rfl u n)
      (continuousOn_const.mul (Complex.continuous_ofReal.comp_continuousOn
        (uRad_continuousOn hk n.natAbs _))) Ioo_subset_Icc_self
    rw [closure_Ioo (by norm_num : (1 / 2 : ℝ) ≠ 1)]
  refine ⟨c, ?_⟩
  intro r hr
  rcases hr.2.eq_or_lt with heq | hlt
  · subst r
    exact he (by norm_num)
  · exact hc r ⟨hr.1, hlt⟩

/-- Boundary Fourier data determines every nonzero regular radial mode.
The zero mode has vanishing boundary value and is intentionally excluded. -/
lemma puncturedDiskMode_nonzero_boundary_formula {k : ℕ} (hk : 2 ≤ k)
    (u : ComplexH1) (n : ℤ) (hn : n ≠ 0)
    (hu : ∀ v : ComplexH1, v ∈ zeroTraceDomain Set.univ →
      weakJacobi (surfacePotential k) u v = 0) :
    ∀ r ∈ Ioc (0 : ℝ) 1, puncturedDiskMode u n r =
      (circleFourierCoeff (diskTraceCLM u) n / (n.natAbs : ℂ)) * (uRad k n.natAbs r : ℂ) := by
  obtain ⟨c, hc⟩ := puncturedDiskMode_eq_const_mul_uRad_closed hk u n hu
  have hb := hc 1 (by norm_num)
  rw [puncturedDiskMode_one, uRad_one hk] at hb
  have hn' : (n.natAbs : ℂ) ≠ 0 := by
    exact_mod_cast (Int.natAbs_ne_zero.mpr hn)
  have he : circleFourierCoeff (diskTraceCLM u) n / (n.natAbs : ℂ) = c := by
    rw [hb]
    simp only [Complex.ofReal_natCast]
    exact mul_div_cancel_right₀ c hn'
  intro r hr
  rw [he]
  exact hc r hr

lemma weak_dirichlet_nonzero_mode_vanishes {k : ℕ} (hk : 2 ≤ k)
    (u : ComplexH1) (n : ℤ) (hn : n ≠ 0)
    (hu : ∀ v : ComplexH1, v ∈ zeroTraceDomain Set.univ →
      weakJacobi (surfacePotential k) u v = 0)
    (htrace : diskTraceCLM u = 0) :
    ∀ r ∈ Ioc (0 : ℝ) 1, puncturedDiskMode u n r = 0 := by
  intro r hr
  rw [puncturedDiskMode_nonzero_boundary_formula hk u n hn hu r hr,
    ← circleCoefficientCLM_apply, htrace, map_zero, zero_div, zero_mul]

lemma mem_fullZeroTrace_iff (u : ComplexH1) :
    u ∈ zeroTraceDomain Set.univ ↔ diskTraceCLM u = 0 := by
  rw [mem_zeroTraceDomain, Measure.restrict_univ]
  constructor
  · intro h
    exact Lp.ext (h.trans (Lp.coeFn_zero ℂ 2 circleMeasure).symm)
  · intro h
    rw [h]
    exact Lp.coeFn_zero ℂ 2 circleMeasure

/-- Every nonzero angular mode of a full weak Dirichlet radical vector vanishes
on `0 < r ≤ 1`. Reconstructing the field from its modes is a separate result. -/
lemma fullDirichlet_kernel_nonzero_modes {k : ℕ} (hk : 2 ≤ k)
    (u : zeroTraceDomain Set.univ)
    (hu : ∀ v : zeroTraceDomain Set.univ, weakJacobi (surfacePotential k) u v = 0)
    (n : ℤ) (hn : n ≠ 0) :
    ∀ r ∈ Ioc (0 : ℝ) 1, puncturedDiskMode u n r = 0 :=
  weak_dirichlet_nonzero_mode_vanishes hk u n hn
    (fun v hv => hu ⟨v, hv⟩) ((mem_fullZeroTrace_iff u).mp u.property)

end KsIndex.Trace
