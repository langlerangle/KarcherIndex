module

public import KsIndexLean.CharDecomp

@[expose] public section


/-!
# Character-projection algebra

For a complex-linear endomorphism `g` on a function space and a submodule `D`,
`charProj_mem` proves that character averaging preserves a `g`-invariant domain.
For positive `N`, `charProj_eq_self` fixes vectors of character `ζ_N^r`.
When `g^N` is the identity on `D`, `charProj_mem_eigenspace` places the average
in that eigenspace by shifting the finite Fourier sum. These results are
algebraic; no continuity, density, or geometric rotation realization is assumed.
-/

noncomputable section
namespace KsIndex.FormIndex
open Module Finset

variable {ι : Type*} (g : Module.End ℂ (ι → ℂ)) {D : Submodule ℂ (ι → ℂ)}

/-- The character projection stays in a `g`-stable domain. -/
lemma charProj_mem (N r : ℕ) (hgD : ∀ u ∈ D, g u ∈ D) (v : ↥D) :
    charProj g N D r v ∈ D := by
  rw [charProj_apply]
  exact D.smul_mem _ (Submodule.sum_mem D fun k _ =>
    D.smul_mem _ (gpow_mem g hgD k v v.2))

/-- The character projection fixes class-`r` vectors. -/
lemma charProj_eq_self {N r : ℕ} (hN : 0 < N) {v : ↥D}
    (hv : g (v : ι → ℂ) = zeta N ^ r • (v : ι → ℂ)) :
    charProj g N D r v = (v : ι → ℂ) := by
  rw [charProj_apply]
  have h1 : ∀ k ∈ range N, xi N ^ (r * k) • (g ^ k) (v : ι → ℂ) =
      (v : ι → ℂ) := by
    intro k _
    rw [gpow_eigen g hv k, ← pow_mul, smul_smul, mul_comm,
      zeta_pow_mul_xi_pow hN (r * k), one_smul]
  rw [Finset.sum_congr rfl h1, Finset.sum_const, card_range,
    ← Nat.cast_smul_eq_nsmul ℂ, smul_smul,
    inv_mul_cancel₀ (Nat.cast_ne_zero.mpr hN.ne'), one_smul]

/-- **The projection lands in the `ζ_N^r`-eigenspace** (the finite-Fourier
telescope: shifting the sum by one costs exactly `ζ^r`, with the wrap
closed by `g^N = id` on the domain and `ξ^{rN} = 1`). -/
lemma charProj_mem_eigenspace (r : ℕ) {N : ℕ} (hN : 0 < N)
    (hgN : ∀ u ∈ D, (g ^ N) u = u) (_hgD : ∀ u ∈ D, g u ∈ D) (v : ↥D) :
    charProj g N D r v ∈ Module.End.eigenspace g (zeta N ^ r) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hN.ne'
  rw [Module.End.mem_eigenspace_iff, charProj_apply]
  set S : ℕ → (ι → ℂ) := fun j => xi (m + 1) ^ (r * j) • (g ^ j) (v : ι → ℂ)
    with hSdef
  have hterm : ∀ k, g (S k) = zeta (m + 1) ^ r • S (k + 1) := by
    intro k
    simp only [hSdef]
    rw [map_smul, ← Module.End.mul_apply, ← pow_succ', smul_smul]
    congr 1
    -- ξ^{rk} = ζ^r · ξ^{r(k+1)}
    rw [mul_add, mul_one, pow_add, ← mul_assoc, mul_comm (zeta (m + 1) ^ r),
      mul_assoc, zeta_pow_mul_xi_pow hN r, mul_one]
  have hwrap : S (m + 1) = S 0 := by
    simp only [hSdef]
    rw [hgN _ v.2, mul_zero, pow_zero, pow_zero, Module.End.one_apply, one_smul,
      mul_comm r, pow_mul, xi_pow_N hN, one_pow, one_smul]
  calc g ((↑(m + 1) : ℂ)⁻¹ • ∑ k ∈ range (m + 1), S k)
      = (↑(m + 1) : ℂ)⁻¹ • ∑ k ∈ range (m + 1), g (S k) := by
        rw [map_smul, map_sum]
    _ = (↑(m + 1) : ℂ)⁻¹ • ∑ k ∈ range (m + 1),
          zeta (m + 1) ^ r • S (k + 1) := by
        congr 1
        exact Finset.sum_congr rfl fun k _ => hterm k
    _ = zeta (m + 1) ^ r • ((↑(m + 1) : ℂ)⁻¹ •
          ∑ k ∈ range (m + 1), S (k + 1)) := by
        rw [← Finset.smul_sum, smul_comm]
    _ = zeta (m + 1) ^ r • ((↑(m + 1) : ℂ)⁻¹ •
          ∑ k ∈ range (m + 1), S k) := by
        congr 2
        -- Σ_{k<m+1} S (k+1) = Σ_{k<m+1} S k, since S (m+1) = S 0
        have h1 : ∑ i ∈ range (m + 1 + 1), S i =
            (∑ i ∈ range (m + 1), S (i + 1)) + S 0 :=
          Finset.sum_range_succ' S (m + 1)
        have h2 : ∑ i ∈ range (m + 1 + 1), S i =
            (∑ i ∈ range (m + 1), S i) + S (m + 1) :=
          Finset.sum_range_succ S (m + 1)
        have h3 := h1.symm.trans h2
        rw [hwrap] at h3
        exact add_right_cancel h3

end KsIndex.FormIndex
