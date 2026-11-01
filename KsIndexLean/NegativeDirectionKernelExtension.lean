module

public import KsIndexLean.FormEqualityCase

@[expose] public section


noncomputable section
namespace KsIndex.Spectral
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- An isotropic vector orthogonal to a negative direction is radical if its
form-orthogonal complement is nonnegative. -/
lemma form_kernel_of_nonnegative_negative_complement
    (Q : E →L⋆[ℂ] E →L[ℂ] ℂ) (hQ : ∀ u v, star (Q v u) = Q u v)
    (e : E) (he : (Q e e).re < 0)
    (hpos : ∀ v : E, Q e v = 0 → 0 ≤ (Q v v).re)
    (u : E) (heu : Q e u = 0) (hu : (Q u u).re = 0) :
    ∀ v : E, Q u v = 0 := by
  let W : Submodule ℂ E := (Q e).toLinearMap.ker
  have hW : ∀ v ∈ W, 0 ≤ (Q v v).re := fun v hv => hpos v hv
  have hz := form_zero_energy_on_subspace Q hQ W hW heu hu
  have hqe : Q e e ≠ 0 := by
    intro h
    rw [h] at he
    exact (lt_irrefl 0) he
  have hue : Q u e = 0 := by rw [← hQ u e, heu, star_zero]
  intro v
  let c : ℂ := Q e v / Q e e
  have hw : v - c • e ∈ W := by
    change Q e (v - c • e) = 0
    simp only [map_sub, map_smul, smul_eq_mul]
    dsimp [c]
    rw [div_mul_cancel₀ _ hqe, sub_self]
  have h := hz (v - c • e) hw
  simpa only [map_sub, map_smul, smul_eq_mul, hue, mul_zero, sub_zero] using h

/-- Extension of a restricted radical when the smaller domain contains a
negative direction whose ambient orthogonal complement is nonnegative. -/
lemma restricted_kernel_extends_of_negative_complement
    (Q : E →L⋆[ℂ] E →L[ℂ] ℂ) (hQ : ∀ u v, star (Q v u) = Q u v)
    (D : Submodule ℂ E) (e : E) (heD : e ∈ D) (he : (Q e e).re < 0)
    (hpos : ∀ v : E, Q e v = 0 → 0 ≤ (Q v v).re)
    (u : E) (huD : u ∈ D) (hu : ∀ v ∈ D, Q u v = 0) :
    ∀ v : E, Q u v = 0 := by
  apply form_kernel_of_nonnegative_negative_complement Q hQ e he hpos u
  · rw [← hQ e u, hu e heD, star_zero]
  · rw [hu u huD]
    rfl

/-- With at most one negative direction, the orthogonal complement of any
negative vector is nonnegative. -/
lemma nonnegative_complement_of_index_le_one
    (Q : E →L⋆[ℂ] E →L[ℂ] ℂ) (hQ : ∀ u v, star (Q v u) = Q u v)
    (hind : KsIndex.NegativeDensity.negativeIndex (fun u => (Q u u).re) ≤ 1)
    (e : E) (he : (Q e e).re < 0) :
    ∀ v : E, Q e v = 0 → 0 ≤ (Q v v).re := by
  classical
  intro v hev
  by_contra hv
  have hv : (Q v v).re < 0 := lt_of_not_ge hv
  have hve : Q v e = 0 := by rw [← hQ v e, hev, star_zero]
  have hB : KsIndex.NegativeDensity.Sesq (fun x y => Q x y) := {
    addL := by intros; simp
    addR := by intros; simp
    smulL := by intros; simp
    smulR := by intros; simp
    conj := by intro x y; exact (hQ y x).symm
    continuous := Q.continuous.comp continuous_fst |>.clm_apply continuous_snd }
  let f : Fin 2 → E := ![e, v]
  have henergy (a b : ℂ) :
      (Q (a • e + b • v) (a • e + b • v)).re =
        ‖a‖ ^ 2 * (Q e e).re + ‖b‖ ^ 2 * (Q v v).re := by
    simp only [map_add, map_smulₛₗ, add_apply,
      smul_apply, smul_eq_mul, hev, hve, mul_zero, add_zero,
      zero_add]
    simp only [RingHom.id_apply, ← mul_assoc, Complex.mul_conj, Complex.normSq_eq_norm_sq,
      Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, sub_zero]
  have hf : ∀ c : Fin 2 → ℂ, c ≠ 0 →
      (Q (∑ j, c j • f j) (∑ j, c j • f j)).re < 0 := by
    intro c hc
    simp only [Fin.sum_univ_two, f, Matrix.cons_val_zero, Matrix.cons_val_one]
    rw [henergy]
    have h0 : ‖c 0‖ ^ 2 * (Q e e).re ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (sq_nonneg _) he.le
    have h1 : ‖c 1‖ ^ 2 * (Q v v).re ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (sq_nonneg _) hv.le
    by_cases hc0 : c 0 = 0
    · have hc1 : c 1 ≠ 0 := by
        intro h
        apply hc
        ext i
        fin_cases i <;> assumption
      have hn : 0 < ‖c 1‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hc1)
      exact add_neg_of_nonpos_of_neg h0 (mul_neg_of_pos_of_neg hn hv)
    · have hn : 0 < ‖c 0‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hc0)
      exact add_neg_of_neg_of_nonpos (mul_neg_of_pos_of_neg hn he) h1
  obtain ⟨hn, hdim⟩ := KsIndex.NegativeDensity.negative_frame_span hB f hf
  let : FiniteDimensional ℂ (Submodule.span ℂ (Set.range f)) :=
    FiniteDimensional.span_of_finite _ (Set.finite_range f)
  have htwo : (2 : ℕ∞) ≤ KsIndex.NegativeDensity.negativeIndex (fun u => (Q u u).re) := by
    change ((2 : ℕ) : ℕ∞) ≤ _
    rw [← hdim]
    exact le_iSup_of_le _ (le_iSup_of_le hn (le_iSup_of_le inferInstance le_rfl))
  have : (2 : ℕ∞) ≤ 1 := htwo.trans hind
  norm_num at this

/-- Index-one saturation extends every restricted kernel vector to the larger
form domain, provided the smaller domain contains a negative vector. -/
lemma restricted_kernel_extends_of_index_le_one
    (Q : E →L⋆[ℂ] E →L[ℂ] ℂ) (hQ : ∀ u v, star (Q v u) = Q u v)
    (hind : KsIndex.NegativeDensity.negativeIndex (fun u => (Q u u).re) ≤ 1)
    (D : Submodule ℂ E) (e : E) (heD : e ∈ D) (he : (Q e e).re < 0)
    (u : E) (huD : u ∈ D) (hu : ∀ v ∈ D, Q u v = 0) :
    ∀ v : E, Q u v = 0 :=
  restricted_kernel_extends_of_negative_complement Q hQ D e heD he
    (nonnegative_complement_of_index_le_one Q hQ hind e he) u huD hu

/-- A nonzero variational negative index supplies an actual negative vector. -/
lemma exists_negative_of_index_ne_zero
    {X : Type*} [AddCommGroup X] [Module ℂ X] (q : X → ℝ)
    (hi : KsIndex.NegativeDensity.negativeIndex q ≠ 0) :
    ∃ x, q x < 0 := by
  classical
  by_contra h
  push Not at h
  apply hi
  apply le_antisymm _ bot_le
  unfold KsIndex.NegativeDensity.negativeIndex
  refine iSup_le fun W => iSup_le fun hW => iSup_le fun _ => ?_
  have hbot : W = ⊥ := by
    apply le_antisymm _ bot_le
    intro x hx
    change x = 0
    by_contra hn
    exact (not_lt_of_ge (h x)) (hW x hx hn)
  simp [hbot]

/-- Equal index one on nested domains suffices for extension of the smaller
radical to the larger domain. -/
lemma restricted_kernel_extends_of_indices_one
    (Q : E →L⋆[ℂ] E →L[ℂ] ℂ) (hQ : ∀ u v, star (Q v u) = Q u v)
    (hind : KsIndex.NegativeDensity.negativeIndex (fun u => (Q u u).re) ≤ 1)
    (D : Submodule ℂ E)
    (hD : KsIndex.NegativeDensity.negativeIndex (fun u : D => (Q u u).re) ≠ 0)
    (u : E) (huD : u ∈ D) (hu : ∀ v ∈ D, Q u v = 0) :
    ∀ v : E, Q u v = 0 := by
  obtain ⟨e, he⟩ := exists_negative_of_index_ne_zero _ hD
  exact restricted_kernel_extends_of_index_le_one Q hQ hind D e e.property he u huD hu

end KsIndex.Spectral
