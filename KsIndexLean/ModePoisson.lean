module

/-
Finite-mode decomposition `Psi = Hpart + groundR · Gpart`.

Each lattice mode factors as
`fam k r n w = (|ℓ(n)| + groundR k w) · baseMode k r n w`, where `baseMode`
is a holomorphic monomial or its conjugate according to the sign of `ℓ(n)`.
Since `groundR` is real, the same factorization applies to both signs.

For `k ≥ 3` and `1 ≤ r ≤ k−1`, every lattice frequency is nonzero. Dividing the
coefficient `t_n` by `|ℓ(n)|` therefore gives the exact finite-sum decomposition
`Psi_decomp`, for arbitrary truncation `N`, coefficients `t`, and point `w : ℂ`.
`Hpart` uses coefficients `t_n`; `Gpart` uses `t_n / |ℓ(n)|`.

The file also proves global smoothness of both finite sums and the norm formula
for `baseMode`. Identification with Poisson integrals, estimates away from the
boundary support, and truncation-tail bounds are separate results; no decay
estimate is asserted here for arbitrary coefficients.
-/
public import KsIndexLean.ModeWitness
public import KsIndexLean.SlitCutoff

@[expose] public section


noncomputable section

open Real Set Complex
open scoped ContDiff
open KsIndex.Surface KsIndex.SingleDiskBridge KsIndex.SingleDisk KsIndex.ModeDiag
  KsIndex.ModeKit KsIndex.ModeWitness

namespace KsIndex.ModePoisson

variable {k r : ℕ}

/-- The pure harmonic monomial of slot `n`: `w^{|ℓ(n)|}` (holomorphic) or its conjugate. -/
def baseMode (k r : ℕ) (n : ℤ) : ℂ → ℂ :=
  if 0 ≤ lz k r n then (fun w => w ^ (lz k r n).natAbs)
  else conjF (fun w => w ^ (lz k r n).natAbs)

/-- The mode factors as `(|ℓ(n)| + groundR)·baseMode` — uniformly across the sign of `ℓ(n)`
(the conjugate branch works because `groundR` is real). -/
lemma fam_factor (k r : ℕ) (n : ℤ) (w : ℂ) :
    fam k r n w = ((((lz k r n).natAbs : ℝ) + groundR k w : ℝ) : ℂ) * baseMode k r n w := by
  unfold fam baseMode
  split
  · rfl
  · show conjF (modeS k (lz k r n).natAbs) w
      = ((((lz k r n).natAbs : ℝ) + groundR k w : ℝ) : ℂ)
        * conjF (fun w => w ^ (lz k r n).natAbs) w
    simp only [conjF, modeS, map_mul]
    rw [Complex.conj_ofReal]

/-- The harmonic part `Σ_{|n|≤N} t_n·baseMode(n)`. -/
def Hpart (k r N : ℕ) (t : ℤ → ℂ) : ℂ → ℂ :=
  fun w => ∑ i : Fin (2 * N + 1), t (slot N i) • baseMode k r (slot N i) w

/-- The `|ℓ|`-normalized twin `Σ_{|n|≤N} (t_n/|ℓ(n)|)·baseMode(n)`. -/
def Gpart (k r N : ℕ) (t : ℤ → ℂ) : ℂ → ℂ :=
  fun w => ∑ i : Fin (2 * N + 1), coefOf k r t (slot N i) • baseMode k r (slot N i) w

/-- **The decomposition** `Psi = Hpart + groundR·Gpart`. -/
theorem Psi_decomp (hk : 3 ≤ k) (hr1 : 1 ≤ r) (hrk : r ≤ k - 1) (N : ℕ) (t : ℤ → ℂ) (w : ℂ) :
    Psi k r N t w
      = Hpart k r N t w + ((groundR k w : ℝ) : ℂ) * Gpart k r N t w := by
  unfold Psi Hpart Gpart
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  set n := slot N i
  have hℓ1 := one_le_natAbs_lz hk hr1 hrk n
  have hℓ0 : ((lz k r n).natAbs : ℂ) ≠ 0 := by
    rw [Ne, Nat.cast_eq_zero]
    omega
  rw [smul_eq_mul, fam_factor k r n w, coefOf, smul_eq_mul, smul_eq_mul]
  push_cast
  field_simp

/-! ### Smoothness of the parts -/

lemma contDiff_baseMode (k r : ℕ) (n : ℤ) : ContDiff ℝ ∞ (baseMode k r n) := by
  unfold baseMode
  split
  · exact contDiff_id.pow _
  · exact contDiff_conjF (contDiff_id.pow _)

lemma contDiff_Hpart (k r N : ℕ) (t : ℤ → ℂ) : ContDiff ℝ ∞ (Hpart k r N t) := by
  unfold Hpart
  exact ContDiff.sum (fun i _ => (contDiff_baseMode k r (slot N i)).const_smul _)

lemma contDiff_Gpart (k r N : ℕ) (t : ℤ → ℂ) : ContDiff ℝ ∞ (Gpart k r N t) := by
  unfold Gpart
  exact ContDiff.sum (fun i _ => (contDiff_baseMode k r (slot N i)).const_smul _)

/-! ### The pure harmonic monomial in polar form -/

/-- For every `w : ℂ`, `‖baseMode k r n w‖ = ‖w‖^{|ℓ(n)|}`. -/
lemma norm_baseMode (k r : ℕ) (n : ℤ) (w : ℂ) :
    ‖baseMode k r n w‖ = ‖w‖ ^ (lz k r n).natAbs := by
  unfold baseMode
  split
  · rw [norm_pow]
  · show ‖conjF (fun w => w ^ (lz k r n).natAbs) w‖ = ‖w‖ ^ (lz k r n).natAbs
    simp only [conjF, RCLike.norm_conj, norm_pow]

end KsIndex.ModePoisson
