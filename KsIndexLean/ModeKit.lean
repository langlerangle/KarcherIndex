module

/-
Smooth uncut modes, rotation characters and diagonal energies.

The radial shift identity `gRad k ℓ = ℓ + gRad k 0` gives the representation
`modeS k ℓ w = (ℓ + groundR k w) * w^ℓ`. The function `modeS` is globally smooth
for all natural `k,ℓ`; its identification with `modeU` assumes `k ≥ 1`.
No cutoff is included in these modes.

The modes are equivariant under every unit complex rotation, not just a finite
rotation subgroup. Complex conjugation gives the opposite character. For `k ≥ 2`
and `ℓ ≥ 1`, the diagonal energy and its conjugate counterpart are
`Qd k (modeS k ℓ) = 2π * ℓ² * sigma k ℓ`.

The abstract pairing lemma `Bd_eq_zero_of_equivariant` proves vanishing when two
smooth disk fields have a paired rotation character `conj(α) * β ≠ 1`.
`exists_char` supplies a unit complex number with `a^m = −1` for any nonzero
integer `m`. Together these are inputs to off-diagonal orthogonality arguments;
the assembly of finite witnesses is performed separately.
-/
public import KsIndexLean.SeamLowerConj
public import KsIndexLean.SlitCutoff

@[expose] public section


noncomputable section

open Real Set Complex
open scoped ContDiff
open KsIndex.Surface KsIndex.JacobiMode KsIndex.SingleDiskBridge KsIndex.Radial
  KsIndex.SingleDisk KsIndex.ModeDiag KsIndex.FormIndex

namespace KsIndex.ModeKit

variable {k : ℕ}

/-! ### The ℓ-shift and the globally smooth mode -/

/-- `gRad k ℓ = ℓ + gRad k 0`: the radial profile is the ground profile shifted by `ℓ`. -/
lemma gRad_shift (k ℓ : ℕ) (r : ℝ) : gRad k ℓ r = (ℓ : ℝ) + gRad k 0 r := by
  unfold gRad
  have hx : (0:ℝ) ≤ r ^ (2 * k - 2) := by
    rw [show 2 * k - 2 = 2 * (k - 1) by omega, pow_mul]
    positivity
  have hden : (0:ℝ) < r ^ (2 * k - 2) + 1 := by linarith
  rw [div_eq_iff hden.ne', add_mul, div_mul_cancel₀ _ hden.ne']
  push_cast
  ring

/-- The raw mode in its globally smooth form: `(ℓ + groundR)·w^ℓ`. -/
def modeS (k ℓ : ℕ) (w : ℂ) : ℂ := (((ℓ : ℝ) + groundR k w : ℝ) : ℂ) * w ^ ℓ

lemma modeS_eq_modeU (hk : 1 ≤ k) (ℓ : ℕ) : modeS k ℓ = modeU k ℓ := by
  funext w
  rw [modeS, modeU, groundR_eq hk, ← gRad_shift]

lemma contDiff_modeS (k ℓ : ℕ) : ContDiff ℝ ∞ (modeS k ℓ) := by
  have h1 : ContDiff ℝ ∞ (fun w : ℂ => (((ℓ : ℝ) + groundR k w : ℝ) : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp (contDiff_const.add (contDiff_groundR k))
  exact h1.mul (contDiff_id.pow ℓ)

/-! ### Full-circle rotation equivariance -/

lemma groundR_rot {a : ℂ} (ha : ‖a‖ = 1) (w : ℂ) : groundR k (a * w) = groundR k w := by
  have key : ∀ z : ℂ, z.re ^ 2 + z.im ^ 2 = Complex.normSq z := fun z => by
    rw [Complex.normSq_apply]; ring
  have hs : (a * w).re ^ 2 + (a * w).im ^ 2 = w.re ^ 2 + w.im ^ 2 := by
    rw [key, key, Complex.normSq_mul,
      show Complex.normSq a = 1 by rw [Complex.normSq_eq_norm_sq, ha]; norm_num, one_mul]
  unfold groundR
  rw [hs]

/-- Full-circle equivariance: `rot1 a (modeS k ℓ) = a^ℓ • modeS k ℓ`. -/
lemma rot1_modeS {a : ℂ} (ha : ‖a‖ = 1) (k ℓ : ℕ) :
    rot1 a (modeS k ℓ) = a ^ ℓ • modeS k ℓ := by
  funext w
  simp only [rot1_apply, Pi.smul_apply, smul_eq_mul, modeS, groundR_rot ha, mul_pow]
  ring

/-- Conjugate twin: `rot1 a (conjF (modeS k ℓ)) = conj(a^ℓ) • conjF (modeS k ℓ)`. -/
lemma rot1_conjF_modeS {a : ℂ} (ha : ‖a‖ = 1) (k ℓ : ℕ) :
    rot1 a (conjF (modeS k ℓ)) = (starRingEnd ℂ) (a ^ ℓ) • conjF (modeS k ℓ) := by
  funext w
  have h := congrFun (rot1_modeS ha k ℓ) w
  simp only [rot1_apply, Pi.smul_apply, smul_eq_mul] at h
  simp only [rot1_apply, conjF, Pi.smul_apply, smul_eq_mul, h, map_mul]

/-! ### The diagonal energies -/

/-- `Qd (modeS k ℓ) = 2π·ℓ²·σ_k(ℓ)`. -/
theorem Qd_modeS (hk : 2 ≤ k) {ℓ : ℕ} (hℓ : 1 ≤ ℓ) :
    Qd k (modeS k ℓ) = 2 * Real.pi * ((ℓ : ℝ) ^ 2 * sigma k ℓ) := by
  have hk1 : 1 ≤ k := by omega
  rw [modeS_eq_modeU hk1]
  have hQ : Qd k (modeU k ℓ) = (∫ w in disk, gradSq (modeU k ℓ) w)
      - ∫ w in disk, potV k w * ‖modeU k ℓ w‖ ^ 2 := by
    unfold Qd
    exact dirichletG_sub_potentialG hk _
  rw [hQ, ← MeasureTheory.integral_sub (integrableOn_gradSq_modeU hk hℓ)
    (integrableOn_potMode hk ℓ)]
  exact modeU_disk_energy hk hℓ

/-- The conjugate mode has the same energy. -/
theorem Qd_conjF_modeS (hk : 2 ≤ k) {ℓ : ℕ} (hℓ : 1 ≤ ℓ) :
    Qd k (conjF (modeS k ℓ)) = 2 * Real.pi * ((ℓ : ℝ) ^ 2 * sigma k ℓ) := by
  rw [Qd_conjF, Qd_modeS hk hℓ]

/-! ### The character-vanishing engine -/

/-- An equivariant pair with nontrivial paired character has vanishing `Bd`. -/
lemma Bd_eq_zero_of_equivariant {f g : ℂ → ℂ} (hf : ContDiffOn ℝ ∞ f disk)
    (hg : ContDiffOn ℝ ∞ g disk) {a α β : ℂ} (ha : ‖a‖ = 1)
    (hrf : rot1 a f = α • f) (hrg : rot1 a g = β • g)
    (hne : (starRingEnd ℂ) α * β ≠ 1) : Bd k f g = 0 := by
  have h := Bd_rot1 (k := k) ha hf hg
  rw [hrf, hrg, Bd_const_smul_left hf, Bd_const_smul_right hg, ← mul_assoc] at h
  have h2 : ((starRingEnd ℂ) α * β - 1) * Bd k f g = 0 := by linear_combination h
  rcases mul_eq_zero.mp h2 with h' | h'
  · exact absurd (by linear_combination h' : (starRingEnd ℂ) α * β = 1) hne
  · exact h'

/-- The character supply: for `m ≠ 0` there is a unimodular `a` with `a^m = −1`. -/
lemma exists_char (m : ℤ) (hm : m ≠ 0) : ∃ a : ℂ, ‖a‖ = 1 ∧ a ^ m = (-1 : ℂ) := by
  refine ⟨Complex.exp ((((Real.pi / m : ℝ)) : ℂ) * Complex.I), ?_, ?_⟩
  · exact Complex.norm_exp_ofReal_mul_I _
  · rw [← Complex.exp_int_mul]
    rw [show (m : ℂ) * ((((Real.pi / m : ℝ)) : ℂ) * Complex.I)
        = ((Real.pi : ℝ) : ℂ) * Complex.I by
      have hm' : (m : ℂ) ≠ 0 := Int.cast_ne_zero.mpr hm
      push_cast
      field_simp]
    exact Complex.exp_pi_mul_I

end KsIndex.ModeKit
