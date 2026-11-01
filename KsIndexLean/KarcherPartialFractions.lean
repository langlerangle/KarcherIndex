module

public import KsIndexLean.KarcherNumerators

@[expose] public section


/-! Polynomial interpolation identities first; actual partial fractions only off the punctures. -/
open Polynomial
open scoped BigOperators
noncomputable section
namespace KsIndex.KarcherData

/-- Interpolate on the actual simple root set. The polynomial part is proved absent. -/
lemma polynomial_identity_of_residue_values {k : ℕ} (hk : 2 ≤ k) (N : ℂ[X])
    (hdeg : N.degree < ↑(2 * k)) (R : ℂ → ℂ)
    (hR : ∀ z ∈ punctureFinset k, N.eval z / denominatorDeriv k z = R z) :
    N = ∑ z ∈ punctureFinset k, C (R z) * ∏ w ∈ (punctureFinset k).erase z, (X - C w) := by
  classical
  have hdeg' : N.degree < ↑(punctureFinset k).card := by rwa [punctureFinset_card hk]
  rw [Lagrange.eq_interpolate (v := id) Function.injective_id.injOn hdeg',
    Lagrange.interpolate_eq_nodalWeight_mul_nodal_div_X_sub_C]
  apply Finset.sum_congr rfl
  intro z hz
  rw [← Lagrange.nodal_erase_eq_nodal_div (v := id) hz,
    nodalWeight_eq_inv_denominatorDeriv hk hz]
  have hc : (denominatorDeriv k z)⁻¹ * N.eval z = R z := by
    simpa only [div_eq_mul_inv, mul_comm] using hR z hz
  change C ((denominatorDeriv k z)⁻¹) * Lagrange.nodal ((punctureFinset k).erase z) id *
    C (N.eval z) = _
  rw [mul_right_comm, ← map_mul, hc]
  rfl

lemma numeratorPoly1_identity {k : ℕ} (hk : 2 ≤ k) :
    numeratorPoly1 k = ∑ z ∈ punctureFinset k,
      C (-(z.re : ℂ)) * ∏ w ∈ (punctureFinset k).erase z, (X - C w) := by
  apply polynomial_identity_of_residue_values hk _ (numeratorPoly1_degree hk)
  intro z hz
  rw [numeratorPoly1_eval hk]
  exact residue1_value hk ((mem_punctureFinset hk).mp hz)
lemma numeratorPoly2_identity {k : ℕ} (hk : 2 ≤ k) :
    numeratorPoly2 k = ∑ z ∈ punctureFinset k,
      C (z.im : ℂ) * ∏ w ∈ (punctureFinset k).erase z, (X - C w) := by
  apply polynomial_identity_of_residue_values hk _ (numeratorPoly2_degree hk)
  intro z hz
  rw [numeratorPoly2_eval hk]
  exact residue2_value hk ((mem_punctureFinset hk).mp hz)
lemma numeratorPoly3_identity {k : ℕ} (hk : 2 ≤ k) :
    numeratorPoly3 k = ∑ z ∈ punctureFinset k,
      C (1 / z ^ k) * ∏ w ∈ (punctureFinset k).erase z, (X - C w) := by
  apply polynomial_identity_of_residue_values hk _ (numeratorPoly3_degree hk)
  intro z hz
  rw [numeratorPoly3_eval]
  exact residue3_value hk ((mem_punctureFinset hk).mp hz)

/-- Evaluate the proved polynomial identity, then divide by nonzero actual factors. -/
lemma partial_fractions_of_polynomial_identity {k : ℕ} (hk : 2 ≤ k) (N : ℂ[X]) (R : ℂ → ℂ)
    (hp : N = ∑ z ∈ punctureFinset k,
      C (R z) * ∏ u ∈ (punctureFinset k).erase z, (X - C u))
    {w : ℂ} (hw : w ∉ Surface.punctures k) :
    N.eval w / (denominatorPoly k).eval w = ∑ z ∈ punctureFinset k, R z / (w - z) := by
  classical
  have hn : ∀ z ∈ punctureFinset k, w - z ≠ 0 := by
    intro z hz he
    exact hw ((sub_eq_zero.mp he) ▸ (mem_punctureFinset hk).mp hz)
  have he := congrArg (fun p : ℂ[X] => p.eval w) hp
  simp only [eval_finsetSum, eval_mul, eval_C, eval_prod, eval_sub, eval_X] at he
  rw [he, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro z hz
  have hprod : (∏ u ∈ (punctureFinset k).erase z, (w - u)) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr (fun u hu => hn u (Finset.mem_of_mem_erase hu))
  have hd : (denominatorPoly k).eval w =
      (w - z) * ∏ u ∈ (punctureFinset k).erase z, (w - u) := by
    rw [denominatorPoly_factorization hk]
    simp only [eval_prod, eval_sub, eval_X, eval_C]
    exact (Finset.mul_prod_erase _ _ hz).symm
  rw [hd]
  field_simp

/-- The existing first coefficient equals the actual finite sum of its normalized residues. -/
theorem coeff1_partial_fractions {k : ℕ} (hk : 2 ≤ k) {w : ℂ}
    (hw : w ∉ Surface.punctures k) :
    coeff1 k w = ∑ z ∈ punctureFinset k, (-(z.re : ℂ)) / (w - z) := by
  rw [← numeratorPoly1_div_eq_coeff1 hk]
  exact partial_fractions_of_polynomial_identity hk _ _ (numeratorPoly1_identity hk) hw

theorem coeff2_partial_fractions {k : ℕ} (hk : 2 ≤ k) {w : ℂ}
    (hw : w ∉ Surface.punctures k) :
    coeff2 k w = ∑ z ∈ punctureFinset k, (z.im : ℂ) / (w - z) := by
  rw [← numeratorPoly2_div_eq_coeff2 hk]
  exact partial_fractions_of_polynomial_identity hk _ _ (numeratorPoly2_identity hk) hw

theorem coeff3_partial_fractions {k : ℕ} (hk : 2 ≤ k) {w : ℂ}
    (hw : w ∉ Surface.punctures k) :
    coeff3 k w = ∑ z ∈ punctureFinset k, (1 / z ^ k) / (w - z) := by
  rw [← numeratorPoly3_div_eq_coeff3]
  exact partial_fractions_of_polynomial_identity hk _ _ (numeratorPoly3_identity hk) hw

end KsIndex.KarcherData
