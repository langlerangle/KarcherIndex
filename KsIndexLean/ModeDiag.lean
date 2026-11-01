module

/-
KsIndexLean — ModeDiag: the single-disk Jacobi pairing and the mode Gram matrix.

`Bd k f g` is the difference of the gradient and potential pairings. For `k ≥ 2`,
its diagonal equals `Qd k f`. Rotation symmetry makes distinct modes orthogonal;
for positive mode degree `ℓ`, the diagonal entry is `2π ℓ² σ_k(ℓ)`, where
`σ_k(ℓ) = (ℓ² - (k - 1)²) / ℓ`.

The file proves integrability of the cross gradient and potential densities,
then expands finite sums of positive-degree modes and diagonalizes their Jacobi
energy. These identities supply the mode energies used in index lower bounds.
The final lemmas prove that the radial profiles and modes are smooth on all of
`ℂ` for `k ≥ 1`, including the origin.
-/
public import KsIndexLean.GradOrtho
public import KsIndexLean.SingleDiskBridge

@[expose] public section


noncomputable section

open Complex MeasureTheory Filter
open scoped ContDiff

namespace KsIndex.ModeDiag

open KsIndex.Surface KsIndex.GradOrtho KsIndex.ThetaOrtho KsIndex.JacobiMode
  KsIndex.SingleDiskBridge KsIndex.Radial

variable {k : ℕ}

/-- The single-disk polarized Jacobi form: `∫_D ⟨∇f,∇g⟩ − ∫_D V_k · conj f · g`.  Its diagonal is
`Qd k` for `k ≥ 2` (`Bd_self_eq_Qd`), and it is Hermitian. Linearity of
finite mode sums is established below using differentiability and integrability. -/
def Bd (k : ℕ) (f g : ℂ → ℂ) : ℂ :=
  (∫ w in disk, gradInner f g w) - ∫ w in disk, (potV k w : ℂ) * (starRingEnd ℂ) (f w) * g w

/-- **Hermitian symmetry**: `conj (Bd f g) = Bd g f`. -/
lemma Bd_conj_symm (f g : ℂ → ℂ) : (starRingEnd ℂ) (Bd k f g) = Bd k g f := by
  unfold Bd
  rw [map_sub, ← integral_conj, ← integral_conj]
  congr 1
  · exact integral_congr_ae (Eventually.of_forall fun w => by
      simp only [gradInner, map_add, map_mul, Complex.conj_conj]; ring)
  · refine integral_congr_ae (Eventually.of_forall fun w => ?_)
    simp only [map_mul, Complex.conj_conj, Complex.conj_ofReal]
    ring

/-- **The diagonal is `Qd`**: `Bd k f f = Qd k f`. -/
lemma Bd_self_eq_Qd (hk : 2 ≤ k) (f : ℂ → ℂ) : Bd k f f = (Qd k f : ℂ) := by
  have hQ : Qd k f = (∫ w in disk, gradSq f w) - ∫ w in disk, potV k w * ‖f w‖ ^ 2 := by
    unfold Qd; exact dirichletG_sub_potentialG hk f
  rw [Bd, hQ, Complex.ofReal_sub]
  have e1 : (∫ w in disk, ((gradSq f w : ℝ) : ℂ))
      = ((∫ w in disk, gradSq f w : ℝ) : ℂ) := integral_ofReal
  have e2 : (∫ w in disk, ((potV k w * ‖f w‖ ^ 2 : ℝ) : ℂ))
      = ((∫ w in disk, potV k w * ‖f w‖ ^ 2 : ℝ) : ℂ) := integral_ofReal
  rw [← e1, ← e2]
  congr 1
  · exact integral_congr_ae (Eventually.of_forall fun w => gradInner_self f w)
  · refine integral_congr_ae (Eventually.of_forall fun w => ?_)
    push_cast
    rw [mul_assoc, Complex.conj_mul']

/-- **Off-diagonal vanishing**: distinct modes are `Bd`-orthogonal.  Both the gradient and the
potential cross integrals vanish by rotational symmetry (`disk_offdiag_gradInner`,
`disk_offdiag_potV`), so no cross-density integrability is needed. -/
lemma Bd_modeU_offdiag (hk : 2 ≤ k) {ℓ ℓ' : ℕ} (hne : ℓ ≠ ℓ') :
    Bd k (modeU k ℓ) (modeU k ℓ') = 0 := by
  unfold Bd
  rw [disk_offdiag_gradInner hk ℓ' ℓ (Ne.symm hne), disk_offdiag_potV k ℓ' ℓ (Ne.symm hne),
    sub_zero]

/-- **The diagonal entry**: `Bd k (modeU ℓ) (modeU ℓ) = 2π ℓ² σ_k(ℓ)`. -/
lemma Bd_modeU_diag (hk : 2 ≤ k) {ℓ : ℕ} (hℓ : 1 ≤ ℓ) :
    Bd k (modeU k ℓ) (modeU k ℓ) = ((2 * Real.pi * ((ℓ : ℝ) ^ 2 * sigma k ℓ) : ℝ) : ℂ) := by
  rw [Bd_self_eq_Qd hk]
  unfold Qd
  rw [modeU_jacobiQ_summand hk hℓ]

/-! ### Integrability of the cross gradient density via Cauchy–Schwarz -/

/-- `|gradInner f g| ≤ (gradSq f + gradSq g)/2` pointwise. -/
lemma norm_gradInner_le (f g : ℂ → ℂ) (w : ℂ) :
    ‖gradInner f g w‖ ≤ (gradSq f w + gradSq g w) / 2 := by
  unfold gradInner gradSq
  set a := fderiv ℝ f w 1; set b := fderiv ℝ g w 1
  set c := fderiv ℝ f w Complex.I; set d := fderiv ℝ g w Complex.I
  calc ‖(starRingEnd ℂ) a * b + (starRingEnd ℂ) c * d‖
      ≤ ‖(starRingEnd ℂ) a * b‖ + ‖(starRingEnd ℂ) c * d‖ := norm_add_le _ _
    _ = ‖a‖ * ‖b‖ + ‖c‖ * ‖d‖ := by rw [norm_mul, norm_mul, Complex.norm_conj, Complex.norm_conj]
    _ ≤ (‖a‖ ^ 2 + ‖c‖ ^ 2 + (‖b‖ ^ 2 + ‖d‖ ^ 2)) / 2 := by
        nlinarith [sq_nonneg (‖a‖ - ‖b‖), sq_nonneg (‖c‖ - ‖d‖)]

/-- The cross gradient density of two modes is integrable on the disk. -/
lemma integrableOn_gradInner_modeU (hk : 2 ≤ k) {ℓ ℓ' : ℕ} (hℓ : 1 ≤ ℓ) (hℓ' : 1 ≤ ℓ') :
    IntegrableOn (gradInner (modeU k ℓ) (modeU k ℓ')) disk := by
  have hbound : IntegrableOn (fun w => (gradSq (modeU k ℓ) w + gradSq (modeU k ℓ') w) / 2) disk :=
    ((integrableOn_gradSq_modeU hk hℓ).add (integrableOn_gradSq_modeU hk hℓ')).div_const 2
  refine hbound.mono' (KsIndex.SurfaceForm.measurable_gradInner _ _).aestronglyMeasurable ?_
  exact Filter.Eventually.of_forall fun w => norm_gradInner_le _ _ w

/-- The potential cross density of two modes is integrable on the disk. -/
lemma integrableOn_potCross_modeU (hk : 2 ≤ k) (ℓ ℓ' : ℕ) :
    IntegrableOn (fun w => (potV k w : ℂ) * (starRingEnd ℂ) (modeU k ℓ w) * modeU k ℓ' w) disk :=
  integrableOn_offdiag hk ℓ' ℓ

/-! ### The finite-sum diagonalization -/

/-- A finite combination of modes `Σ_{ℓ∈S} c_ℓ · modeU_ℓ`. -/
def modeSum (k : ℕ) (S : Finset ℕ) (c : ℕ → ℂ) : ℂ → ℂ :=
  fun w => ∑ ℓ ∈ S, c ℓ • modeU k ℓ w

lemma fderiv_modeSum (hk : 2 ≤ k) (S : Finset ℕ) (c : ℕ → ℂ) {w : ℂ} (hw : w ≠ 0) :
    fderiv ℝ (modeSum k S c) w = ∑ ℓ ∈ S, c ℓ • fderiv ℝ (modeU k ℓ) w := by
  unfold modeSum
  rw [fderiv_fun_sum (A := fun ℓ y => c ℓ • modeU k ℓ y)
    fun ℓ _ => (modeU_differentiableAt hk ℓ hw).const_smul (c ℓ)]
  exact Finset.sum_congr rfl fun ℓ _ => fderiv_fun_const_smul (modeU_differentiableAt hk ℓ hw) _

/-- Pointwise (off `0`): the gradient density of a mode sum expands into the cross densities. -/
lemma gradInner_modeSum (hk : 2 ≤ k) (S : Finset ℕ) (c : ℕ → ℂ) {w : ℂ} (hw : w ≠ 0) :
    gradInner (modeSum k S c) (modeSum k S c) w
      = ∑ ℓ ∈ S, ∑ m ∈ S, (starRingEnd ℂ) (c ℓ) * c m * gradInner (modeU k ℓ) (modeU k m) w := by
  simp only [gradInner, fderiv_modeSum hk S c hw, sum_apply,
    smul_apply, smul_eq_mul, map_sum, map_mul, Finset.sum_mul_sum]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun ℓ _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun m _ => ?_
  ring

/-- Pointwise: the potential density of a mode sum expands into the cross densities. -/
lemma potDens_modeSum (k : ℕ) (S : Finset ℕ) (c : ℕ → ℂ) (w : ℂ) :
    (potV k w : ℂ) * (starRingEnd ℂ) (modeSum k S c w) * modeSum k S c w
      = ∑ ℓ ∈ S, ∑ m ∈ S, (starRingEnd ℂ) (c ℓ) * c m
          * ((potV k w : ℂ) * (starRingEnd ℂ) (modeU k ℓ w) * modeU k m w) := by
  simp only [modeSum, smul_eq_mul, map_sum, map_mul, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun ℓ _ => Finset.sum_congr rfl fun m _ => ?_
  ring

/-- **`Bd` of a mode sum is the Gram double sum.** -/
lemma Bd_modeSum (hk : 2 ≤ k) (S : Finset ℕ) (hS : ∀ ℓ ∈ S, 1 ≤ ℓ) (c : ℕ → ℂ) :
    Bd k (modeSum k S c) (modeSum k S c)
      = ∑ ℓ ∈ S, ∑ m ∈ S, (starRingEnd ℂ) (c ℓ) * c m * Bd k (modeU k ℓ) (modeU k m) := by
  have h0 : ∀ᵐ w ∂(volume.restrict disk), w ≠ (0 : ℂ) :=
    ae_restrict_of_ae (by rw [ae_iff]; simp)
  have hg : ∫ w in disk, gradInner (modeSum k S c) (modeSum k S c) w
      = ∑ ℓ ∈ S, ∑ m ∈ S, (starRingEnd ℂ) (c ℓ) * c m
          * ∫ w in disk, gradInner (modeU k ℓ) (modeU k m) w := by
    rw [integral_congr_ae (g := fun w => ∑ ℓ ∈ S, ∑ m ∈ S,
        (starRingEnd ℂ) (c ℓ) * c m * gradInner (modeU k ℓ) (modeU k m) w)
      (by filter_upwards [h0] with w hw using gradInner_modeSum hk S c hw)]
    rw [integral_finsetSum _ fun ℓ hℓ => integrable_finsetSum _ fun m hm =>
      (integrableOn_gradInner_modeU hk (hS ℓ hℓ) (hS m hm)).const_mul _]
    refine Finset.sum_congr rfl fun ℓ hℓ => ?_
    rw [integral_finsetSum _ fun m hm =>
      (integrableOn_gradInner_modeU hk (hS ℓ hℓ) (hS m hm)).const_mul _]
    exact Finset.sum_congr rfl fun m _ => integral_const_mul _ _
  have hp : ∫ w in disk, (potV k w : ℂ) * (starRingEnd ℂ) (modeSum k S c w) * modeSum k S c w
      = ∑ ℓ ∈ S, ∑ m ∈ S, (starRingEnd ℂ) (c ℓ) * c m
          * ∫ w in disk, (potV k w : ℂ) * (starRingEnd ℂ) (modeU k ℓ w) * modeU k m w := by
    simp_rw [potDens_modeSum k S c]
    rw [integral_finsetSum _ fun ℓ _ => integrable_finsetSum _ fun m _ =>
      (integrableOn_potCross_modeU hk ℓ m).const_mul _]
    refine Finset.sum_congr rfl fun ℓ _ => ?_
    rw [integral_finsetSum _ fun m _ => (integrableOn_potCross_modeU hk ℓ m).const_mul _]
    exact Finset.sum_congr rfl fun m _ => integral_const_mul _ _
  unfold Bd
  rw [hg, hp, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun ℓ _ => ?_
  rw [← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun m _ => by ring

/-- **The finite-sum diagonalization**:
`Qd(Σ_{ℓ∈S} c_ℓ modeU_ℓ) = Σ_{ℓ∈S} |c_ℓ|² · 2π ℓ² σ_k(ℓ)`. -/
theorem Qd_modeSum (hk : 2 ≤ k) (S : Finset ℕ) (hS : ∀ ℓ ∈ S, 1 ≤ ℓ) (c : ℕ → ℂ) :
    Qd k (modeSum k S c)
      = ∑ ℓ ∈ S, ‖c ℓ‖ ^ 2 * (2 * Real.pi * ((ℓ : ℝ) ^ 2 * sigma k ℓ)) := by
  have h := Bd_modeSum hk S hS c
  rw [Bd_self_eq_Qd hk] at h
  have h2 : ∀ ℓ ∈ S, ∑ m ∈ S, (starRingEnd ℂ) (c ℓ) * c m * Bd k (modeU k ℓ) (modeU k m)
      = ((‖c ℓ‖ ^ 2 * (2 * Real.pi * ((ℓ : ℝ) ^ 2 * sigma k ℓ)) : ℝ) : ℂ) := by
    intro ℓ hℓ
    rw [Finset.sum_eq_single_of_mem ℓ hℓ
      (fun m _ hm => by rw [Bd_modeU_offdiag hk (Ne.symm hm), mul_zero])]
    rw [Bd_modeU_diag hk (hS ℓ hℓ), Complex.conj_mul']
    push_cast; ring
  rw [Finset.sum_congr rfl h2] at h
  exact_mod_cast h

/-! ### Smoothness of the modes on all of `ℂ` -/

/-- `‖w‖^{2k−2} = normSq (w^{k−1})` (even power of the norm is a polynomial in `w`). -/
lemma norm_pow_normSq {k : ℕ} (hk : 1 ≤ k) (w : ℂ) :
    ‖w‖ ^ (2 * k - 2) = Complex.normSq (w ^ (k - 1)) := by
  have h : 2 * k - 2 = 2 * (k - 1) := by omega
  rw [h, Complex.normSq_eq_norm_sq, norm_pow, ← pow_mul, mul_comm]

/-- The radial profile `w ↦ gRad k ℓ ‖w‖` is `C^∞` on `ℂ` — a rational function of the polynomial
`normSq (w^{k−1})` with nonvanishing denominator. -/
lemma contDiff_gRad_norm (k ℓ : ℕ) (hk : 1 ≤ k) :
    ContDiff ℝ ∞ (fun w : ℂ => KsIndex.Radial.gRad k ℓ ‖w‖) := by
  have hP : ContDiff ℝ ∞ (fun w : ℂ => Complex.normSq (w ^ (k - 1))) := by
    have hf : ContDiff ℝ ∞ (fun w : ℂ => w ^ (k - 1)) := contDiff_id.pow _
    have hre := Complex.reCLM.contDiff.comp hf
    have him := Complex.imCLM.contDiff.comp hf
    simpa [Complex.normSq_apply] using (hre.mul hre).add (him.mul him)
  have hden : ∀ w : ℂ, Complex.normSq (w ^ (k - 1)) + 1 ≠ 0 := fun w => by
    have := Complex.normSq_nonneg (w ^ (k - 1)); positivity
  have heq : (fun w : ℂ => KsIndex.Radial.gRad k ℓ ‖w‖)
      = fun w => (((ℓ : ℝ) + KsIndex.Radial.kap k)
            + ((ℓ : ℝ) - KsIndex.Radial.kap k) * Complex.normSq (w ^ (k - 1)))
          / (Complex.normSq (w ^ (k - 1)) + 1) := by
    funext w; unfold KsIndex.Radial.gRad; rw [norm_pow_normSq hk w]
  rw [heq]
  exact (contDiff_const.add (contDiff_const.mul hP)).div (hP.add contDiff_const) hden

/-- **The mode `modeU k ℓ` is `C^∞` on all of `ℂ`.** -/
lemma modeU_contDiff {k : ℕ} (hk : 1 ≤ k) (ℓ : ℕ) : ContDiff ℝ ∞ (modeU k ℓ) := by
  have : (fun w : ℂ => (KsIndex.Radial.gRad k ℓ ‖w‖ : ℂ) * w ^ ℓ) = modeU k ℓ := rfl
  rw [← this]
  exact (Complex.ofRealCLM.contDiff.comp (contDiff_gRad_norm k ℓ hk)).mul (contDiff_id.pow ℓ)

end KsIndex.ModeDiag
