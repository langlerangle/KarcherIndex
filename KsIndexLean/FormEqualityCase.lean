module

public import KsIndexLean.HermitianZeroEnergy
public import KsIndexLean.JacobiRadicalSpectrum

@[expose] public section


noncomputable section
namespace KsIndex.Spectral
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- A bundled Hermitian form has zero pairing on a nonnegative subspace
whenever a vector in that subspace has zero energy. -/
lemma form_zero_energy_on_subspace (Q : E →L⋆[ℂ] E →L[ℂ] ℂ)
    (hQ : ∀ u v, star (Q v u) = Q u v) (W : Submodule ℂ E)
    (hn : ∀ u ∈ W, 0 ≤ (Q u u).re) {u : E} (hu : u ∈ W)
    (hz : (Q u u).re = 0) : ∀ v ∈ W, Q u v = 0 := by
  apply KsIndex.hermitian_orthogonal_of_nonneg_diag (fun u v => Q u v) W
    (fun x _ y _ z _ => by simp)
    (fun x _ y _ z _ => by simp)
    (fun c x _ y _ => by simp)
    (fun x _ y _ => ?_) hn hu hz
  exact (hQ y x).symm

/-- Saturation of a lower bound gives the full weak eigenfunction equation on
that same subspace. It does not enlarge the test domain. -/
lemma form_lower_bound_equality (Q M : E →L⋆[ℂ] E →L[ℂ] ℂ)
    (hQ : ∀ u v, star (Q v u) = Q u v)
    (hM : ∀ u v, star (M v u) = M u v)
    (W : Submodule ℂ E) (L : ℝ)
    (hlower : ∀ u ∈ W, L * (M u u).re ≤ (Q u u).re)
    {u : E} (hu : u ∈ W) (heq : (Q u u).re = L * (M u u).re) :
    ∀ v ∈ W, Q u v = (L : ℂ) * M u v := by
  let A := Q - (L : ℂ) • M
  have ha (x y : E) : A x y = Q x y - (L : ℂ) * M x y := by simp [A]
  have herm (x y : E) : star (A y x) = A x y := by
    simp only [ha, star_sub, star_mul, hQ, hM]
    simp [mul_comm]
  have hn (x : E) (hx : x ∈ W) : 0 ≤ (A x x).re := by
    rw [ha]
    simpa using sub_nonneg.mpr (hlower x hx)
  have hz : (A u u).re = 0 := by rw [ha]; simpa using sub_eq_zero.mpr heq
  intro v hv
  have h := form_zero_energy_on_subspace A herm W hn hu hz v hv
  rw [ha, sub_eq_zero] at h
  exact h

/-- When the lower bound holds on the whole form domain, equality gives an
unrestricted weak equation on that domain. -/
lemma form_lower_bound_equality_global (Q M : E →L⋆[ℂ] E →L[ℂ] ℂ)
    (hQ : ∀ u v, star (Q v u) = Q u v)
    (hM : ∀ u v, star (M v u) = M u v) (L : ℝ)
    (hlower : ∀ u, L * (M u u).re ≤ (Q u u).re)
    {u : E} (heq : (Q u u).re = L * (M u u).re) :
    ∀ v, Q u v = (L : ℂ) * M u v := by
  intro v
  exact form_lower_bound_equality Q M hQ hM ⊤ L (fun x _ => hlower x)
    (Submodule.mem_top) heq v (Submodule.mem_top)

/-- Mass-orthogonality to a weak eigenvector also kills the form pairing.
This supplies the omitted low-mode test directions in the complement argument. -/
lemma form_pairing_zero_of_weak_eigenvector (Q M : E →L⋆[ℂ] E →L[ℂ] ℂ)
    (hQ : ∀ u v, star (Q v u) = Q u v)
    (hM : ∀ u v, star (M v u) = M u v)
    (e u : E) (μ : ℂ) (hev : ∀ v, Q e v = μ * M e v)
    (horth : M u e = 0) : Q u e = 0 := by
  rw [← hQ u e, hev u, ← hM e u, horth]
  simp

/-- Equality on a spectral complement gives a full weak eigenfunction once
the complementary test directions also satisfy the same equation. This is
the explicit domain-extension step needed for higher eigenvalue equality. -/
lemma form_lower_bound_equality_of_sup (Q M : E →L⋆[ℂ] E →L[ℂ] ℂ)
    (hQ : ∀ u v, star (Q v u) = Q u v)
    (hM : ∀ u v, star (M v u) = M u v)
    (U W : Submodule ℂ E) (hcover : U ⊔ W = ⊤) (L : ℝ)
    (hlower : ∀ x ∈ W, L * (M x x).re ≤ (Q x x).re)
    {u : E} (hu : u ∈ W) (heq : (Q u u).re = L * (M u u).re)
    (hU : ∀ v ∈ U, Q u v = (L : ℂ) * M u v) :
    ∀ v, Q u v = (L : ℂ) * M u v := by
  intro v
  have hv : v ∈ U ⊔ W := by rw [hcover]; exact Submodule.mem_top
  obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hv
  rw [map_add, map_add, hU a ha,
    form_lower_bound_equality Q M hQ hM W L hlower hu heq b hb, mul_add]

/-- Nested-domain transport preserves the attained energy. If the larger
form has the same lower bound, the image satisfies its full weak equation.
Together with the smaller-domain equation this gives a common eigenfunction;
nonzeroness follows from injectivity of the inclusion. -/
lemma common_weak_equation_of_attained_bound
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
    (Q M : E →L⋆[ℂ] E →L[ℂ] ℂ) (R N : F →L⋆[ℂ] F →L[ℂ] ℂ)
    (hR : ∀ x y, star (R y x) = R x y)
    (hN : ∀ x y, star (N y x) = N x y)
    (T : E →ₗ[ℂ] F) (hT : Function.Injective T)
    (hform : ∀ x y, R (T x) (T y) = Q x y)
    (hmass : ∀ x y, N (T x) (T y) = M x y)
    (L : ℝ) (hlower : ∀ x, L * (N x x).re ≤ (R x x).re)
    {u : E} (hu : u ≠ 0) (heq : ∀ v, Q u v = (L : ℂ) * M u v) :
    T u ≠ 0 ∧ (∀ v, Q u v = (L : ℂ) * M u v) ∧
      ∀ w, R (T u) w = (L : ℂ) * N (T u) w := by
  refine ⟨fun hz => hu (hT (hz.trans T.map_zero.symm)), heq, ?_⟩
  apply form_lower_bound_equality_global R N hR hN L hlower
  rw [hform, hmass, heq u]
  simp

end KsIndex.Spectral
