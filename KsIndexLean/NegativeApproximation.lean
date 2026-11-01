module

/-
Finite-dimensional negativity preservation under matrix approximation.
Entrywise error bounds preserve a uniform negative margin. Strict negativity
supplies such a margin by compactness of the Euclidean unit sphere. These are
finite-dimensional estimates; density and index transport are separate results.
-/
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Topology.Order.Compact
public import Mathlib.Data.Matrix.Basic
public import Mathlib.Tactic

@[expose] public section


noncomputable section

open Complex Finset

namespace KsIndex.NegativeApproximation

/-- Real quadratic expression of a complex matrix, with conjugate first slot. -/
def quadratic {d : ℕ} (A : Matrix (Fin d) (Fin d) ℂ) (c : Fin d → ℂ) : ℝ :=
  (∑ i, ∑ j, (starRingEnd ℂ) (c i) * A i j * c j).re

/-- Squared Euclidean coefficient norm. -/
def energy {d : ℕ} (c : Fin d → ℂ) : ℝ := ∑ i, ‖c i‖ ^ 2

lemma energy_nonneg {d : ℕ} (c : Fin d → ℂ) : 0 ≤ energy c := by
  exact Finset.sum_nonneg fun _ _ => sq_nonneg _

lemma quadratic_zero {d : ℕ} (A : Matrix (Fin d) (Fin d) ℂ) : quadratic A 0 = 0 := by
  simp [quadratic]

lemma quadratic_sub {d : ℕ} (A C : Matrix (Fin d) (Fin d) ℂ) (c : Fin d → ℂ) :
    quadratic (C - A) c = quadratic C c - quadratic A c := by
  simp [quadratic, Matrix.sub_apply, mul_sub, sub_mul, Finset.sum_sub_distrib]

lemma abs_quadratic_le {d : ℕ} (A : Matrix (Fin d) (Fin d) ℂ) (c : Fin d → ℂ) :
    |quadratic A c| ≤ ∑ i, ∑ j, ‖A i j‖ * ‖c i‖ * ‖c j‖ := by
  calc
    _ ≤ ‖∑ i, ∑ j, (starRingEnd ℂ) (c i) * A i j * c j‖ := Complex.abs_re_le_norm _
    _ ≤ ∑ i, ‖∑ j, (starRingEnd ℂ) (c i) * A i j * c j‖ := norm_sum_le _ _
    _ ≤ ∑ i, ∑ j, ‖(starRingEnd ℂ) (c i) * A i j * c j‖ :=
      Finset.sum_le_sum fun _ _ => norm_sum_le _ _
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      simp only [norm_mul, Complex.norm_conj]
      ring

lemma sum_norm_sq_le {d : ℕ} (c : Fin d → ℂ) :
    (∑ i, ‖c i‖) ^ 2 ≤ (d : ℝ) * energy c := by
  simpa [energy] using
    (Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (Fin d))
      (fun _ => (1 : ℝ)) (fun i => ‖c i‖))

/-- Entrywise matrix errors control the quadratic expression uniformly on
coefficient vectors. No Hermitian assumption is needed for this bound. -/
lemma quadratic_error_le {d : ℕ} {A C : Matrix (Fin d) (Fin d) ℂ} {ε : ℝ}
    (hε : 0 ≤ ε) (hAC : ∀ i j, ‖C i j - A i j‖ ≤ ε) (c : Fin d → ℂ) :
    |quadratic C c - quadratic A c| ≤ ε * (d : ℝ) * energy c := by
  rw [← quadratic_sub]
  calc
    _ ≤ ∑ i, ∑ j, ‖(C - A) i j‖ * ‖c i‖ * ‖c j‖ := abs_quadratic_le _ _
    _ ≤ ∑ i, ∑ j, ε * ‖c i‖ * ‖c j‖ := by
      apply Finset.sum_le_sum
      intro i _
      apply Finset.sum_le_sum
      intro j _
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (hAC i j) (norm_nonneg _)) (norm_nonneg _)
    _ = ε * (∑ i, ‖c i‖) ^ 2 := by
      simp only [Finset.mul_sum, Finset.sum_mul, pow_two]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      ring
    _ ≤ ε * ((d : ℝ) * energy c) := mul_le_mul_of_nonneg_left (sum_norm_sq_le c) hε
    _ = _ := by ring

/-- Entrywise tolerance delta/(2d) preserves at least half the uniform
negative margin. Dimension zero is excluded from this division-based statement. -/
theorem negative_margin_of_entrywise_close {d : ℕ} (hd : 1 ≤ d)
    {A C : Matrix (Fin d) (Fin d) ℂ} {δ : ℝ} (hδ : 0 < δ)
    (hA : ∀ c, quadratic A c ≤ -δ * energy c)
    (hAC : ∀ i j, ‖C i j - A i j‖ ≤ δ / (2 * (d : ℝ))) :
    ∀ c, quadratic C c ≤ -(δ / 2) * energy c := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
  intro c
  have he := quadratic_error_le (by positivity : 0 ≤ δ / (2 * (d : ℝ))) hAC c
  have he' : quadratic C c - quadratic A c ≤ δ / 2 * energy c := by
    calc
      _ ≤ |quadratic C c - quadratic A c| := le_abs_self _
      _ ≤ δ / (2 * (d : ℝ)) * (d : ℝ) * energy c := he
      _ = δ / 2 * energy c := by field_simp [ne_of_gt hdR]
  linarith [hA c]

/-- Finite matrix quadratic expressions are continuous without a separate
continuity hypothesis. EuclideanSpace fixes the coefficient norm to the L2 norm. -/
lemma continuous_quadratic {d : ℕ} (A : Matrix (Fin d) (Fin d) ℂ) :
    Continuous (fun x : EuclideanSpace ℂ (Fin d) => quadratic A (fun i => x i)) := by
  unfold quadratic
  fun_prop

lemma quadratic_real_smul {d : ℕ} (A : Matrix (Fin d) (Fin d) ℂ)
    (c : Fin d → ℂ) (r : ℝ) : quadratic A (r • c) = r ^ 2 * quadratic A c := by
  have h : (∑ i, ∑ j, (starRingEnd ℂ) ((r • c) i) * A i j * (r • c) j)
      = (r : ℂ) ^ 2 * ∑ i, ∑ j, (starRingEnd ℂ) (c i) * A i j * c j := by
    simp only [Pi.smul_apply, Complex.real_smul, map_mul, Complex.conj_ofReal,
      Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  unfold quadratic
  rw [h, ← Complex.ofReal_pow]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]

/-- Strict negativity of a finite matrix quadratic expression has a
uniform Euclidean negative margin, by compactness of the unit sphere.
This statement also covers dimension zero (the sphere may be empty). -/
theorem exists_uniform_negative_margin {d : ℕ} (A : Matrix (Fin d) (Fin d) ℂ)
    (hA : ∀ c : Fin d → ℂ, c ≠ 0 → quadratic A c < 0) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ c : Fin d → ℂ, quadratic A c ≤ -δ * energy c := by
  let q : EuclideanSpace ℂ (Fin d) → ℝ := fun x => quadratic A (fun i => x i)
  have hq : Continuous q := continuous_quadratic A
  have hs : ∀ x ∈ Metric.sphere (0 : EuclideanSpace ℂ (Fin d)) 1, 0 < -q x := by
    intro x hx
    have hxnorm : ‖x‖ = 1 := by simpa using hx
    have hxc : (fun i => x i) ≠ 0 := by
      intro hz
      have hx0 : x = 0 := by ext i; exact congrFun hz i
      simp [hx0] at hxnorm
    exact neg_pos.mpr (hA _ hxc)
  have hcompact := isCompact_sphere (0 : EuclideanSpace ℂ (Fin d)) 1
  obtain ⟨δ, hδ, hbound⟩ := hcompact.exists_forall_le' hq.neg.continuousOn hs
  refine ⟨δ, hδ, fun c => ?_⟩
  let x : EuclideanSpace ℂ (Fin d) := WithLp.toLp 2 c
  have hxenergy : ‖x‖ ^ 2 = energy c := EuclideanSpace.norm_sq_eq x
  by_cases hx0 : x = 0
  · have hc0 : c = 0 := by funext i; exact congrArg (fun y : EuclideanSpace ℂ (Fin d) => y i) hx0
    simp [hc0, quadratic_zero, energy]
  · have hr : 0 < ‖x‖ := norm_pos_iff.mpr hx0
    let y : EuclideanSpace ℂ (Fin d) := ‖x‖⁻¹ • x
    have hy : y ∈ Metric.sphere (0 : EuclideanSpace ℂ (Fin d)) 1 := by
      simp [y, norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hr.le), hr.ne']
    have hb := hbound y hy
    change δ ≤ -q y at hb
    have hqy : q y = (‖x‖⁻¹) ^ 2 * quadratic A c := by
      exact quadratic_real_smul A c ‖x‖⁻¹
    rw [hqy] at hb
    have hm := mul_le_mul_of_nonneg_left hb (sq_nonneg ‖x‖)
    have he : ‖x‖ ^ 2 * (‖x‖⁻¹) ^ 2 = 1 := by field_simp [hr.ne']
    rw [mul_neg, ← mul_assoc, he, one_mul] at hm
    rw [← hxenergy]
    nlinarith

end KsIndex.NegativeApproximation
