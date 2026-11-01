module

public import Mathlib

@[expose] public section


noncomputable section
namespace KsIndex.InvariantHermitian

variable {E : Type*} [AddCommGroup E] [Module ℂ E]

/-- The sum `X + R X`. It is invariant when `R` is an involution, and
finite-dimensional when `X` is finite-dimensional. -/
def invariantHull (R : Module.End ℂ E) (X : Submodule ℂ E) : Submodule ℂ E :=
  X ⊔ X.map R

lemma le_invariantHull (R : Module.End ℂ E) (X : Submodule ℂ E) :
    X ≤ invariantHull R X := le_sup_left

lemma invariantHull_stable (R : Module.End ℂ E) (hR : Function.Involutive R)
    (X : Submodule ℂ E) {u : E} (hu : u ∈ invariantHull R X) :
    R u ∈ invariantHull R X := by
  obtain ⟨x, hx, y, hy, rfl⟩ := Submodule.mem_sup.mp hu
  obtain ⟨z, hz, rfl⟩ := Submodule.mem_map.mp hy
  rw [map_add, hR]
  exact Submodule.add_mem _ ((show X.map R ≤ invariantHull R X from le_sup_right) (Submodule.mem_map.mpr ⟨x, hx, rfl⟩))
    ((le_invariantHull R X) hz)

instance invariantHull_finite (R : Module.End ℂ E) (X : Submodule ℂ E)
    [FiniteDimensional ℂ X] : FiniteDimensional ℂ (invariantHull R X) := by
  unfold invariantHull
  infer_instance

def hullInvolution (R : Module.End ℂ E) (hR : Function.Involutive R)
    (X : Submodule ℂ E) : Module.End ℂ (invariantHull R X) :=
  R.restrict (fun _u hu => invariantHull_stable R hR X hu)

lemma hullInvolution_involutive (R : Module.End ℂ E) (hR : Function.Involutive R)
    (X : Submodule ℂ E) : Function.Involutive (hullInvolution R hR X) := by
  intro u
  exact Subtype.ext (hR u.val)

/-- The inclusion of `X` into `X + R X`. Its underlying vectors are unchanged,
so restricting any form preserves its values on the image. -/
def intoHull (R : Module.End ℂ E) (X : Submodule ℂ E) : X →ₗ[ℂ] invariantHull R X :=
  Submodule.inclusion (le_invariantHull R X)

lemma intoHull_injective (R : Module.End ℂ E) (X : Submodule ℂ E) :
    Function.Injective (intoHull R X) := Submodule.inclusion_injective _

section InnerProduct
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- A unitary involution preserving a represented Hermitian form commutes
with its representing operator. This is the spectral step's exact input. -/
lemma representingOperator_commutes (T R : Module.End ℂ H)
    (hR : Function.Involutive R)
    (hunit : ∀ u v, inner ℂ (R u) (R v) = inner ℂ u v)
    (hform : ∀ u v, inner ℂ (R u) (T (R v)) = inner ℂ u (T v)) :
    Function.Commute T R := by
  intro v
  apply ext_inner_left ℂ
  intro u
  calc inner ℂ u (T (R v))
      = inner ℂ (R (R u)) (T (R v)) := by rw [hR]
    _ = inner ℂ (R u) (T v) := hform (R u) v
    _ = inner ℂ (R (R u)) (R (T v)) := (hunit (R u) (T v)).symm
    _ = inner ℂ u (R (T v)) := by rw [hR]

/-- Commutation preserves each spectral eigenspace, including the negative
ones used in the paper's finite-dimensional argument. -/
lemma eigenspace_stable_of_commute (T R : Module.End ℂ H)
    (hcomm : Function.Commute T R) (μ : ℂ) {u : H}
    (hu : u ∈ Module.End.eigenspace T μ) : R u ∈ Module.End.eigenspace T μ := by
  apply Module.End.mem_eigenspace_iff.mpr
  rw [hcomm u, Module.End.mem_eigenspace_iff.mp hu, map_smul]

/-- The entire strictly negative spectral subspace, allowing repeated eigenvalues. -/
def negativeSpectralSpace (T : Module.End ℂ H) : Submodule ℂ H :=
  ⨆ μ : {r : ℝ // r < 0}, Module.End.eigenspace T (μ.val : ℂ)

lemma negativeSpectralSpace_stable (T R : Module.End ℂ H)
    (hcomm : Function.Commute T R) :
    ∀ u ∈ negativeSpectralSpace T, R u ∈ negativeSpectralSpace T := by
  change negativeSpectralSpace T ≤ (negativeSpectralSpace T).comap R
  apply iSup_le
  intro μ u hu
  exact (le_iSup (fun ν : {r : ℝ // r < 0} => Module.End.eigenspace T (ν.val : ℂ)) μ)
    (eigenspace_stable_of_commute T R hcomm μ.val hu)

section FiniteSpectral
variable [FiniteDimensional ℂ H]

/-- The diagonal energy identity from the finite-dimensional spectral theorem. -/
lemma symmetric_energy_spectral_sum (T : Module.End ℂ H) (hT : T.IsSymmetric) (u : H) :
    (inner ℂ u (T u)).re = ∑ i : Fin (Module.finrank ℂ H),
      hT.eigenvalues rfl i * ‖(hT.eigenvectorBasis rfl).repr u i‖ ^ 2 := by
  classical
  let b := hT.eigenvectorBasis rfl
  rw [← b.sum_inner_mul_inner u (T u), Complex.re_sum]
  apply Finset.sum_congr rfl
  intro i hi
  have he := hT.eigenvectorBasis_apply_self_apply rfl u i
  rw [b.repr_apply_apply, b.repr_apply_apply] at he
  rw [he, ← inner_conj_symm u (b i)]
  change ((starRingEnd ℂ) (inner ℂ (b i) u) *
    ((hT.eigenvalues rfl i : ℂ) * inner ℂ (b i) u)).re = _
  rw [← mul_assoc, mul_comm ((starRingEnd ℂ) _) _, mul_assoc,
    mul_comm ((starRingEnd ℂ) (inner ℂ (b i) u)), Complex.mul_conj, Complex.normSq_eq_norm_sq]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
  rw [b.repr_apply_apply]

/-- A vector orthogonal to every negative eigenvector has nonnegative energy. -/
lemma nonnegative_of_negative_coordinates_zero (T : Module.End ℂ H) (hT : T.IsSymmetric)
    (u : H) (hu : ∀ i, hT.eigenvalues rfl i < 0 →
      (hT.eigenvectorBasis rfl).repr u i = 0) : 0 ≤ (inner ℂ u (T u)).re := by
  rw [symmetric_energy_spectral_sum T hT u]
  apply Finset.sum_nonneg
  intro i hi
  by_cases h : hT.eigenvalues rfl i < 0
  · rw [hu i h, norm_zero, zero_pow (by decide : 2 ≠ 0), mul_zero]
  · exact mul_nonneg (le_of_not_gt h) (sq_nonneg _)

/-- Spectral-theorem bound on any negative trial space, without any rank-one
assumption on the eventual blocks. -/
lemma negative_trial_finrank_le_spectral_count (T : Module.End ℂ H) (hT : T.IsSymmetric)
    (X : Submodule ℂ H)
    (hX : ∀ u : X, u ≠ 0 → (inner ℂ u.val (T u.val)).re < 0) :
    Module.finrank ℂ X ≤ Fintype.card {i : Fin (Module.finrank ℂ H) // hT.eigenvalues rfl i < 0} := by
  classical
  let I := {i : Fin (Module.finrank ℂ H) // hT.eigenvalues rfl i < 0}
  let b := hT.eigenvectorBasis rfl
  let f : X →ₗ[ℂ] (I → ℂ) := LinearMap.pi (fun i =>
    (b.toBasis.coord i.val).comp X.subtype)
  have hf : Function.Injective f := by
    apply (LinearMap.ker_eq_bot).mp
    apply le_antisymm ?_ bot_le
    intro u hu
    change u = 0
    by_contra hne
    have hz : f u = 0 := hu
    have hn := nonnegative_of_negative_coordinates_zero T hT u.val (by
      intro i hi
      exact congrFun hz ⟨i, hi⟩)
    exact (not_lt_of_ge hn) (hX u hne)
  have h := LinearMap.finrank_le_finrank_of_injective hf
  simpa only [Module.finrank_pi, Module.finrank_self, Finset.sum_const, Finset.card_univ,
    smul_eq_mul, mul_one] using h

end FiniteSpectral

end InnerProduct
end KsIndex.InvariantHermitian
