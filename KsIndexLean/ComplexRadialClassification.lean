module

public import KsIndexLean.RadialMode

@[expose] public section


noncomputable section
namespace KsIndex.Radial
open Set

/-- Complex regular radial solutions have one complex degree of freedom.
The regularity and mode ODE hypotheses are explicit; this theorem alone does
not assert regularity of a weak disk solution. -/
lemma eq_const_mul_uRad_complex {k : ℕ} (hk : 2 ≤ k) (ℓ : ℕ) {f f' : ℝ → ℂ}
    (hfc : ContinuousOn f (Ico 0 1)) (hf'c : ContinuousOn f' (Ico 0 1))
    (hd : ∀ r ∈ Ioo (0:ℝ) 1, HasDerivAt f (f' r) r)
    (hode : ∀ r ∈ Ioo (0:ℝ) 1,
      HasDerivAt (fun r : ℝ => (r : ℂ) * f' r)
        (((ℓ : ℂ) ^ 2 * f r / (r : ℂ)) - (r : ℂ) * (Vrad k r : ℂ) * f r) r) :
    ∃ c : ℂ, ∀ r ∈ Ico (0:ℝ) 1, f r = c * (uRad k ℓ r : ℂ) := by
  have hre : ∀ r ∈ Ioo (0:ℝ) 1,
      HasDerivAt (fun r => r * (f' r).re)
        ((ℓ : ℝ)^2 * (f r).re / r - r * Vrad k r * (f r).re) r := by
    intro r hr
    simpa [pow_two] using hasDerivAt_re (hode r hr)
  have him : ∀ r ∈ Ioo (0:ℝ) 1,
      HasDerivAt (fun r => r * (f' r).im)
        ((ℓ : ℝ)^2 * (f r).im / r - r * Vrad k r * (f r).im) r := by
    intro r hr
    simpa [pow_two] using hasDerivAt_im (hode r hr)
  obtain ⟨a, ha⟩ := eq_const_mul_uRad hk ℓ
    (Complex.continuous_re.comp_continuousOn hfc)
    (Complex.continuous_re.comp_continuousOn hf'c)
    (fun r hr => hasDerivAt_re (hd r hr)) hre
  obtain ⟨b, hb⟩ := eq_const_mul_uRad hk ℓ
    (Complex.continuous_im.comp_continuousOn hfc)
    (Complex.continuous_im.comp_continuousOn hf'c)
    (fun r hr => hasDerivAt_im (hd r hr)) him
  refine ⟨⟨a,b⟩, fun r hr => ?_⟩
  apply Complex.ext
  · simpa using ha r hr
  · simpa using hb r hr

/-- Continuity extends the regular-mode classification to the outer boundary. -/
lemma eq_const_mul_uRad_complex_closed {k : ℕ} (hk : 2 ≤ k) (ℓ : ℕ) {f f' : ℝ → ℂ}
    (hfc : ContinuousOn f (Icc 0 1)) (hf'c : ContinuousOn f' (Ico 0 1))
    (hd : ∀ r ∈ Ioo (0:ℝ) 1, HasDerivAt f (f' r) r)
    (hode : ∀ r ∈ Ioo (0:ℝ) 1,
      HasDerivAt (fun r : ℝ => (r : ℂ) * f' r)
        (((ℓ : ℂ) ^ 2 * f r / (r : ℂ)) - (r : ℂ) * (Vrad k r : ℂ) * f r) r) :
    ∃ c : ℂ, ∀ r ∈ Icc (0:ℝ) 1, f r = c * (uRad k ℓ r : ℂ) := by
  obtain ⟨c, hc⟩ := eq_const_mul_uRad_complex hk ℓ (hfc.mono Ico_subset_Icc_self) hf'c hd hode
  refine ⟨c, Set.EqOn.of_subset_closure hc hfc ?_ Ico_subset_Icc_self ?_⟩
  · exact continuousOn_const.mul
      (Complex.continuous_ofReal.comp_continuousOn (uRad_continuousOn hk ℓ _))
  · rw [closure_Ico (by norm_num : (0 : ℝ) ≠ 1)]

/-- Dirichlet data kills every nonzero regular angular mode. The zero angular
mode is deliberately retained: it is the vertical Jacobi field. -/
lemma regular_dirichlet_nonzero_mode_vanishes {k ℓ : ℕ} (hk : 2 ≤ k) (hℓ : ℓ ≠ 0)
    {f f' : ℝ → ℂ} (hfc : ContinuousOn f (Icc 0 1))
    (hf'c : ContinuousOn f' (Ico 0 1))
    (hd : ∀ r ∈ Ioo (0:ℝ) 1, HasDerivAt f (f' r) r)
    (hode : ∀ r ∈ Ioo (0:ℝ) 1,
      HasDerivAt (fun r : ℝ => (r : ℂ) * f' r)
        (((ℓ : ℂ) ^ 2 * f r / (r : ℂ)) - (r : ℂ) * (Vrad k r : ℂ) * f r) r)
    (hb : f 1 = 0) : ∀ r ∈ Icc (0:ℝ) 1, f r = 0 := by
  obtain ⟨c, hc⟩ := eq_const_mul_uRad_complex_closed hk ℓ hfc hf'c hd hode
  have he := hc 1 (by norm_num)
  rw [hb, uRad_one hk] at he
  have hn : ((ℓ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hℓ
  have hz : c = 0 := (mul_eq_zero.mp he.symm).resolve_right hn
  intro r hr
  rw [hc r hr, hz, zero_mul]

end KsIndex.Radial
