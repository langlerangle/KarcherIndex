module

/-
# Character decomposition under a finite-order form symmetry

Let `g` be a complex-linear endomorphism of a function space and `D` a complex
submodule. Assume `N > 0`, `g(D) ⊆ D`, and `g^N u = u` for `u ∈ D`, together
with the `Sesq Q B D` form hypotheses and invariance `B (g u) (g v) = B u v`
on `D`. Periodicity is required only on the domain.

The subspaces `D ⊓ eigenspace g (ζ_N^r)`, indexed by `r : Fin N`, form an
orthogonal decomposition for `B`. Their averaging projections are
`P_r v = (1/N) ∑_{j<N} conjugate(ζ_N)^(r*j) g^j v`.
Form invariance gives orthogonality of distinct characters; finite geometric
sums give reconstruction and vanishing of projections on the other blocks.

`formIndex_eq_sum_eigen` and `formNullity_eq_sum_eigen` apply the corresponding
orthogonal-sum theorems. No finite-dimensionality assumption on `D` is made.
The construction can be applied successively to commuting symmetries when each
preserves the relevant domain and form, as in the disk-chain sector decomposition.
-/
public import KsIndexLean.FormIndexSum

@[expose] public section


noncomputable section

namespace KsIndex.FormIndex

open Module Finset

variable {ι : Type*}

/-! ### The root of unity and its conjugate -/

/-- `ζ_N = e^{2πi/N}`. -/
def zeta (N : ℕ) : ℂ := Complex.exp (2 * Real.pi * Complex.I / N)

/-- `ζ̄_N = ζ_N⁻¹`, the conjugate root. -/
def xi (N : ℕ) : ℂ := (starRingEnd ℂ) (zeta N)

lemma zeta_prim {N : ℕ} (hN : 0 < N) : IsPrimitiveRoot (zeta N) N :=
  Complex.isPrimitiveRoot_exp N hN.ne'

lemma zeta_pow_N {N : ℕ} (hN : 0 < N) : zeta N ^ N = 1 := (zeta_prim hN).pow_eq_one

lemma zeta_mul_xi {N : ℕ} (hN : 0 < N) : zeta N * xi N = 1 := by
  rw [xi, Complex.mul_conj, Complex.normSq_eq_norm_sq, (zeta_prim hN).norm'_eq_one hN.ne']
  norm_num

lemma zeta_pow_mul_xi_pow {N : ℕ} (hN : 0 < N) (r : ℕ) : zeta N ^ r * xi N ^ r = 1 := by
  rw [← mul_pow, zeta_mul_xi hN, one_pow]

lemma xi_pow_N {N : ℕ} (hN : 0 < N) : xi N ^ N = 1 := by
  rw [xi, ← map_pow, zeta_pow_N hN, map_one]

lemma conj_zeta_pow (N r : ℕ) : (starRingEnd ℂ) (zeta N ^ r) = xi N ^ r := by
  rw [map_pow]; rfl

lemma xi_pow_ne_one {N k : ℕ} (hN : 0 < N) (hk0 : k ≠ 0) (hk : k < N) : xi N ^ k ≠ 1 := by
  intro h
  have h1 : zeta N ^ k = 1 := by
    have := congrArg (starRingEnd ℂ) h
    rw [← conj_zeta_pow, map_one] at this
    simpa using this
  exact (zeta_prim hN).pow_ne_one_of_pos_of_lt hk0 hk h1

/-- The cross-character scalar `ζ̄^a ζ^b` is `≠ 1` for distinct `a, b < N`. -/
lemma xi_pow_mul_zeta_pow_ne_one {N a b : ℕ} (hN : 0 < N) (ha : a < N) (hb : b < N)
    (hab : a ≠ b) : xi N ^ a * zeta N ^ b ≠ 1 := by
  intro heq
  have h1 : zeta N ^ a = zeta N ^ b := by
    calc zeta N ^ a = zeta N ^ a * (xi N ^ a * zeta N ^ b) := by rw [heq, mul_one]
      _ = (zeta N ^ a * xi N ^ a) * zeta N ^ b := by ring
      _ = zeta N ^ b := by rw [zeta_pow_mul_xi_pow hN, one_mul]
  exact hab ((zeta_prim hN).pow_inj ha hb h1)

/-- `∑_{k<N} ω^k = 0` for `ω^N = 1`, `ω ≠ 1`. -/
lemma geom_sum_eq_zero_of_pow_eq_one {ω : ℂ} {N : ℕ} (hω : ω ^ N = 1) (hne : ω ≠ 1) :
    ∑ k ∈ range N, ω ^ k = 0 := by
  have h := geom_sum_mul ω N
  rw [hω, sub_self] at h
  rcases mul_eq_zero.mp h with h0 | h0
  · exact h0
  · exact absurd (sub_eq_zero.mp h0) hne

/-! ### Powers of the symmetry -/

variable (g : Module.End ℂ (ι → ℂ)) {D : Submodule ℂ (ι → ℂ)}

lemma gpow_mem (hgD : ∀ u ∈ D, g u ∈ D) : ∀ k, ∀ u ∈ D, (g ^ k) u ∈ D
  | 0, u, hu => by simpa using hu
  | k + 1, u, hu => by
    rw [pow_succ', Module.End.mul_apply]
    exact hgD _ (gpow_mem hgD k u hu)

lemma gpow_eigen {μ : ℂ} {v : ι → ℂ} (hv : g v = μ • v) : ∀ k, (g ^ k) v = μ ^ k • v
  | 0 => by simp
  | k + 1 => by
    rw [pow_succ', Module.End.mul_apply, gpow_eigen hv k, map_smul, hv, smul_smul, ← pow_succ]

/-! ### The averaging projections -/

/-- The character projection `P r = (1/N) ∑_{k<N} ζ̄^{rk} g^k`, restricted to the domain. -/
def charProj (N : ℕ) (D : Submodule ℂ (ι → ℂ)) (r : ℕ) : ↥D →ₗ[ℂ] (ι → ℂ) :=
  ((N : ℂ)⁻¹ • ∑ k ∈ range N, xi N ^ (r * k) • g ^ k).comp D.subtype

lemma charProj_apply (N : ℕ) (r : ℕ) (v : ↥D) :
    charProj g N D r v = (N : ℂ)⁻¹ • ∑ k ∈ range N, xi N ^ (r * k) • (g ^ k) (v : ι → ℂ) := by
  simp [charProj]

/-! ### The eigenspace decomposition -/

variable {Q : (ι → ℂ) → ℝ} {B : (ι → ℂ) → (ι → ℂ) → ℂ}

/-- **The character decomposition** of a domain under a form-preserving periodic symmetry: the
eigenspaces `D ⊓ eigenspace g (ζ^r)`, `r : Fin N`, with the averaging projections. -/
def eigenDecomp (h : Sesq Q B D) {N : ℕ} (hN : 0 < N)
    (hgN : ∀ u ∈ D, (g ^ N) u = u) (hgD : ∀ u ∈ D, g u ∈ D)
    (hinv : ∀ u ∈ D, ∀ v ∈ D, B (g u) (g v) = B u v) :
    OrthDecomp B D (fun r : Fin N => D ⊓ Module.End.eigenspace g (zeta N ^ (r : ℕ))) where
  le := fun _ => inf_le_left
  orth := by
    intro r s hrs u hu v hv
    obtain ⟨huD, hue⟩ := Submodule.mem_inf.mp hu
    obtain ⟨hvD, hve⟩ := Submodule.mem_inf.mp hv
    rw [Module.End.mem_eigenspace_iff] at hue hve
    have h1 : B u v = (xi N ^ (r : ℕ) * zeta N ^ (s : ℕ)) * B u v := by
      conv_lhs => rw [← hinv u huD v hvD, hue, hve, h.smulR _ (D.smul_mem _ huD) hvD,
        h.smulL _ huD hvD, conj_zeta_pow]
      ring
    have hω : xi N ^ (r : ℕ) * zeta N ^ (s : ℕ) ≠ 1 :=
      xi_pow_mul_zeta_pow_ne_one hN r.2 s.2 (fun e => hrs (Fin.ext e))
    have h3 : (1 - xi N ^ (r : ℕ) * zeta N ^ (s : ℕ)) * B u v = 0 := by linear_combination h1
    rcases mul_eq_zero.mp h3 with h4 | h4
    · exact absurd (sub_eq_zero.mp h4).symm hω
    · exact h4
  P := fun r => charProj g N D r
  P_mem := by
    intro r v
    refine Submodule.mem_inf.mpr ⟨?_, ?_⟩
    · rw [charProj_apply]
      exact D.smul_mem _ (D.sum_mem fun k _ => D.smul_mem _ (gpow_mem g hgD k v v.2))
    · rw [Module.End.mem_eigenspace_iff, charProj_apply, map_smul, map_sum]
      simp only [map_smul]
      rw [smul_smul, mul_comm (zeta N ^ (r : ℕ)) _, ← smul_smul]
      congr 1
      rw [Finset.smul_sum]
      obtain ⟨M, rfl⟩ : ∃ M, N = M + 1 := ⟨N - 1, by omega⟩
      rw [Finset.sum_range_succ, Finset.sum_range_succ']
      congr 1
      · refine Finset.sum_congr rfl fun k _ => ?_
        rw [smul_smul, pow_succ' g, Module.End.mul_apply]
        congr 1
        rw [mul_add, mul_one, pow_add, mul_left_comm, zeta_pow_mul_xi_pow hN, mul_one]
      · rw [← Module.End.mul_apply, ← pow_succ' g, hgN v v.2, mul_zero, pow_zero, one_smul,
          pow_zero, Module.End.one_apply]
        congr 1
        calc xi (M + 1) ^ ((r : ℕ) * M)
            = xi (M + 1) ^ ((r : ℕ) * M) * (xi (M + 1) ^ (r : ℕ) * zeta (M + 1) ^ (r : ℕ)) := by
              rw [mul_comm (xi (M + 1) ^ (r : ℕ)), zeta_pow_mul_xi_pow hN, mul_one]
          _ = xi (M + 1) ^ ((r : ℕ) * (M + 1)) * zeta (M + 1) ^ (r : ℕ) := by ring
          _ = zeta (M + 1) ^ (r : ℕ) := by
              rw [mul_comm (r : ℕ), pow_mul, xi_pow_N hN, one_pow, one_mul]
  P_sum := by
    intro v
    simp only [charProj_apply]
    rw [← Finset.smul_sum,
      Fin.sum_univ_eq_sum_range
        (fun r : ℕ => ∑ k ∈ range N, xi N ^ (r * k) • (g ^ k) (v : ι → ℂ)) N,
      Finset.sum_comm]
    have hinner : ∀ k ∈ range N,
        ∑ r ∈ range N, xi N ^ (r * k) • (g ^ k) (v : ι → ℂ)
          = if k = 0 then (N : ℂ) • (v : ι → ℂ) else 0 := by
      intro k hk
      rw [← Finset.sum_smul]
      have hre : ∑ r ∈ range N, xi N ^ (r * k) = ∑ r ∈ range N, (xi N ^ k) ^ r :=
        Finset.sum_congr rfl fun r _ => by rw [← pow_mul, mul_comm]
      rw [hre]
      split_ifs with hk0
      · subst hk0
        simp [Finset.sum_const, Finset.card_range]
      · have hne : xi N ^ k ≠ 1 := xi_pow_ne_one hN hk0 (Finset.mem_range.mp hk)
        have hpow : (xi N ^ k) ^ N = 1 := by rw [← pow_mul, mul_comm, pow_mul, xi_pow_N hN, one_pow]
        rw [geom_sum_eq_zero_of_pow_eq_one hpow hne, zero_smul]
    rw [Finset.sum_congr rfl hinner, Finset.sum_ite_eq' (range N) 0,
      if_pos (Finset.mem_range.mpr hN), smul_smul,
      inv_mul_cancel₀ (by exact_mod_cast hN.ne' : (N : ℂ) ≠ 0), one_smul]
  P_ne := by
    intro i j hij v hv
    obtain ⟨_, hve⟩ := Submodule.mem_inf.mp hv
    rw [Module.End.mem_eigenspace_iff] at hve
    rw [charProj_apply]
    simp only [gpow_eigen g hve, smul_smul]
    rw [← Finset.sum_smul]
    have hω : ∑ k ∈ range N, xi N ^ ((j : ℕ) * k) * (zeta N ^ (i : ℕ)) ^ k
        = ∑ k ∈ range N, (xi N ^ (j : ℕ) * zeta N ^ (i : ℕ)) ^ k :=
      Finset.sum_congr rfl fun k _ => by rw [mul_pow, pow_mul]
    have hne : xi N ^ (j : ℕ) * zeta N ^ (i : ℕ) ≠ 1 :=
      xi_pow_mul_zeta_pow_ne_one hN j.2 i.2 (fun e => hij (Fin.ext e.symm))
    have hpow : (xi N ^ (j : ℕ) * zeta N ^ (i : ℕ)) ^ N = 1 := by
      rw [mul_pow, ← pow_mul, ← pow_mul, mul_comm (j : ℕ), mul_comm (i : ℕ), pow_mul, pow_mul,
        xi_pow_N hN, zeta_pow_N hN, one_pow, one_pow, mul_one]
    rw [hω, geom_sum_eq_zero_of_pow_eq_one hpow hne, zero_smul, smul_zero]

/-- **Index splits over the eigenspaces** of a form-preserving periodic symmetry. -/
theorem formIndex_eq_sum_eigen (h : Sesq Q B D) {N : ℕ} (hN : 0 < N)
    (hgN : ∀ u ∈ D, (g ^ N) u = u) (hgD : ∀ u ∈ D, g u ∈ D)
    (hinv : ∀ u ∈ D, ∀ v ∈ D, B (g u) (g v) = B u v) :
    formIndex Q D
      = ∑ r : Fin N, formIndex Q (D ⊓ Module.End.eigenspace g (zeta N ^ (r : ℕ))) :=
  formIndex_eq_sum h (eigenDecomp g h hN hgN hgD hinv)

/-- **Nullity splits over the eigenspaces** of a form-preserving periodic symmetry. -/
theorem formNullity_eq_sum_eigen (h : Sesq Q B D) {N : ℕ} (hN : 0 < N)
    (hgN : ∀ u ∈ D, (g ^ N) u = u) (hgD : ∀ u ∈ D, g u ∈ D)
    (hinv : ∀ u ∈ D, ∀ v ∈ D, B (g u) (g v) = B u v) :
    formNullity B D
      = ∑ r : Fin N, formNullity B (D ⊓ Module.End.eigenspace g (zeta N ^ (r : ℕ))) :=
  formNullity_eq_sum h (eigenDecomp g h hN hgN hgD hinv)

end KsIndex.FormIndex
