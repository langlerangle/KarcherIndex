module

public import KsIndexLean.Statements

@[expose] public section


/-! The least eigenvalue of the circle form relative to coefficient mass.
The physical arclength pairing requires separate Fourier normalization. -/
noncomputable section
namespace KsIndex.Statements
open KsIndex.CircleQ

/-- Coefficient mass pairing, conjugate-linear in the first argument. -/
def massPair (u v : ℤ → ℂ) : ℂ := ∑' n : ℤ, (starRingEnd ℂ) (u n) * v n

lemma summable_massPair {u v : ℤ → ℂ} (hu : MemDom u) (hv : MemDom v) :
    Summable (fun n : ℤ => (starRingEnd ℂ) (u n) * v n) := by
  apply Summable.of_norm
  refine ((summable_normSq hu.1).add (summable_normSq hv.1)).of_nonneg_of_le
    (fun n => norm_nonneg _) (fun n => ?_)
  simp only [norm_mul, starRingEnd_apply, norm_star]
  nlinarith [sq_nonneg (‖u n‖ - ‖v n‖), sq_nonneg ‖u n‖, sq_nonneg ‖v n‖]

lemma massPair_self (u : ℤ → ℂ) : massPair u u = (normSq u : ℂ) := by
  simp only [massPair, normSq, Complex.ofReal_tsum]
  apply tsum_congr
  intro n
  rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq]

lemma massPair_conj_symm (u v : ℤ → ℂ) :
    massPair v u = (starRingEnd ℂ) (massPair u v) := by
  rw [massPair, massPair, starRingEnd_apply, tsum_star]
  apply tsum_congr
  intro n
  simp [star_mul, mul_comm]

lemma massPair_add_right {u v w : ℤ → ℂ} (hu : MemDom u)
    (hv : MemDom v) (hw : MemDom w) :
    massPair u (v + w) = massPair u v + massPair u w := by
  rw [massPair, massPair, massPair, ← (summable_massPair hu hv).tsum_add
    (summable_massPair hu hw)]
  apply tsum_congr
  intro n
  simp [mul_add]

lemma massPair_add_left {u v w : ℤ → ℂ} (hu : MemDom u)
    (hv : MemDom v) (hw : MemDom w) :
    massPair (u + v) w = massPair u w + massPair v w := by
  rw [massPair_conj_symm w (u + v), massPair_add_right hw hu hv, map_add,
    ← massPair_conj_symm w u, ← massPair_conj_symm w v]

lemma massPair_smul_right (c : ℂ) (u v : ℤ → ℂ) :
    massPair u (c • v) = c * massPair u v := by
  rw [massPair, massPair, ← tsum_mul_left]
  apply tsum_congr
  intro n
  simp [mul_left_comm]

lemma normSq_add_expand {u w : ℤ → ℂ} (hu : MemDom u) (hw : MemDom w) :
    (normSq (u + w) : ℂ) = (normSq u : ℂ) + massPair u w +
      (starRingEnd ℂ) (massPair u w) + (normSq w : ℂ) := by
  rw [← massPair_self, massPair_add_left hu hw (memDom_add hu hw),
    massPair_add_right hu hu hw, massPair_add_right hw hu hw,
    massPair_conj_symm u w, massPair_self, massPair_self]
  ring

/-- A minimizer of the shifted quadratic form satisfies the full weak equation. -/
lemma eigen_equation_of_minimizer {s : ℝ} {u : ℤ → ℂ} (hu : MemDom u)
    (hmin : Qform s u = gam s * normSq u) :
    ∀ v, MemDom v → Bform s u v = (gam s : ℂ) * massPair u v := by
  have hre : ∀ v, MemDom v → (Bform s u v - (gam s : ℂ) * massPair u v).re = 0 := by
    intro v hv
    refine discriminant_aux (sub_nonneg.mpr (gam_mul_normSq_le (s := s) hv)) fun t => ?_
    have htv := memDom_smul (t : ℂ) hv
    have he := congrArg Complex.re (Qform_add_expand hu htv (s := s))
    have hm := congrArg Complex.re (normSq_add_expand hu htv)
    rw [Bform_smul_right, Qform_smul] at he
    rw [massPair_smul_right, normSq_smul] at hm
    have ht : ‖(t : ℂ)‖ ^ 2 = t ^ 2 := by
      rw [Complex.norm_real, Real.norm_eq_abs, sq_abs]
    rw [ht] at he hm
    simp only [Complex.ofReal_re, Complex.add_re, Complex.conj_re,
      Complex.mul_re, Complex.ofReal_im, zero_mul, sub_zero] at he hm
    have hp := gam_mul_normSq_le (s := s) (memDom_add hu htv)
    simp only [Complex.sub_re, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, sub_zero]
    rw [hm, he, hmin] at hp
    nlinarith
  intro v hv
  have h1 := hre v hv
  have h2 := hre (Complex.I • v) (memDom_smul Complex.I hv)
  rw [Bform_smul_right, massPair_smul_right] at h2
  have hi : (Bform s u v - (gam s : ℂ) * massPair u v).im = 0 := by
    have hc : Complex.I * Bform s u v - (gam s : ℂ) * (Complex.I * massPair u v) =
        Complex.I * (Bform s u v - (gam s : ℂ) * massPair u v) := by ring
    rw [hc] at h2
    simp [Complex.mul_re] at h2 ⊢
    linarith
  exact sub_eq_zero.mp (Complex.ext (by simpa using h1) (by simpa using hi))


/-- For positive parameters, the attained infimum has a normalized eigenvector. -/
theorem exists_least_coefficient_eigenvector {s : ℝ} (hs : 0 < s) :
    ∃ u : ℤ → ℂ, MemDom u ∧ normSq u = 1 ∧ u ≠ 0 ∧
      ∀ v, MemDom v → Bform s v u = (gam s : ℂ) * massPair v u := by
  obtain ⟨u, hu, hn, hq⟩ := exists_minimizer hs
  have he := eigen_equation_of_minimizer hu (by simpa [hn] using hq)
  refine ⟨u, hu, hn, ?_, ?_⟩
  · intro hz
    rw [hz, normSq_zero] at hn
    norm_num at hn
  · intro v hv
    rw [Bform_conj_symm, he v hv, map_mul, Complex.conj_ofReal,
      ← massPair_conj_symm]

/-- The variational infimum is no greater than any coefficient eigenvalue. -/
theorem gam_le_coefficient_eigenvalue {s μ : ℝ} {u : ℤ → ℂ}
    (hu : MemDom u) (hne : u ≠ 0)
    (he : ∀ v, MemDom v → Bform s v u = (μ : ℂ) * massPair v u) :
    gam s ≤ μ := by
  have hself := he u hu
  rw [Bform_self, massPair_self] at hself
  have hreal := congrArg Complex.re hself
  simp only [Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
    mul_zero, sub_zero] at hreal
  have hb := gam_mul_normSq_le (s := s) hu
  have hp := normSq_pos hu hne
  nlinarith
end KsIndex.Statements
