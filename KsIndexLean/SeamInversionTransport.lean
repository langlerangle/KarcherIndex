module

public import KsIndexLean.SphericalInversionJacobian
public import KsIndexLean.GradOrtho
public import KsIndexLean.SurfacePotentialFacts
public import KsIndexLean.PotVSigma
public import Mathlib.MeasureTheory.Function.Jacobian

@[expose] public section


/-!
# Inversion transport of the weak Jacobi pairing

The gradient and potential integrals are invariant under the seam reflection
`σ(w) = 1/w̄` after pulling back both functions. The potential statement holds
for every `potV k` with `k ≥ 2`; the gradient statement is independent of k.

Although σ is anti-conformal, both slots of the sesquilinear gradient density
use the same antilinear derivative. Their cross terms cancel, leaving the
Jacobian weight `‖z‖⁻⁴` without an additional conjugation. For the potential
term, `PotVSigma.potV_sigma` cancels that weight exactly.

The two transports are stated separately. The potential transport requires
no differentiability hypotheses on the functions.
-/

noncomputable section
open Set MeasureTheory
open scoped ContDiff
namespace KsIndex.Trace
open KsIndex.GradOrtho KsIndex.Surface KsIndex.Spherical

/-! ### The sesquilinear antilinear-pullback algebra -/

/-- Both slots of the sesquilinear gradient density composed with the same
antilinear map `v ↦ a·v̄` produce the weight `‖a‖²` and no conjugation flip:
the cross terms cancel. Pure ℝ-linear algebra — holds for arbitrary `A, B`. -/
lemma sesq_antilinear_weight (A B : ℂ →L[ℝ] ℂ) (a : ℂ) :
    starRingEnd ℂ (A a) * B a +
      starRingEnd ℂ (A (-(a * Complex.I))) * B (-(a * Complex.I)) =
      ((‖a‖ ^ 2 : ℝ) : ℂ) *
        (starRingEnd ℂ (A 1) * B 1 +
          starRingEnd ℂ (A Complex.I) * B Complex.I) := by
  obtain ⟨r, s, rfl⟩ : ∃ r s : ℝ, a = (r : ℂ) + (s : ℂ) * Complex.I :=
    ⟨a.re, a.im, (Complex.re_add_im a).symm⟩
  have hn : (‖(r : ℂ) + (s : ℂ) * Complex.I‖ ^ 2 : ℝ) = r ^ 2 + s ^ 2 := by
    rw [Complex.sq_norm]
    simp [Complex.normSq_apply]
    ring
  have h1 : ((r : ℂ) + (s : ℂ) * Complex.I) = (r : ℝ) • (1 : ℂ) + (s : ℝ) • Complex.I := by
    apply Complex.ext <;> simp [Complex.real_smul]
  have h2 : -(((r : ℂ) + (s : ℂ) * Complex.I) * Complex.I) =
      (s : ℝ) • (1 : ℂ) + (-r : ℝ) • Complex.I := by
    apply Complex.ext <;>
      simp [Complex.real_smul, Complex.mul_re, Complex.mul_im]
  have key : ∀ T : ℂ →L[ℝ] ℂ, T ((r : ℂ) + (s : ℂ) * Complex.I) =
      (r : ℂ) * T 1 + (s : ℂ) * T Complex.I := fun T => by
    rw [h1, map_add, map_smul, map_smul, Complex.real_smul, Complex.real_smul]
  have key2 : ∀ T : ℂ →L[ℝ] ℂ, T (-(((r : ℂ) + (s : ℂ) * Complex.I) * Complex.I)) =
      (s : ℂ) * T 1 + -((r : ℂ) * T Complex.I) := fun T => by
    rw [h2, map_add, map_smul, map_smul, Complex.real_smul, Complex.real_smul]
    push_cast
    ring
  rw [hn, key A, key B, key2 A, key2 B]
  simp only [map_add, map_neg, map_mul, Complex.conj_ofReal]
  push_cast
  ring

/-- The pointwise seam pullback of the gradient density: composition with `σ`
in both slots is the plain density at `σ z`, weighted by `‖z‖⁻⁴` — no
conjugation flip. -/
lemma gradInner_comp_sigma {u v : ℂ → ℂ} {z : ℂ} (hz : z ≠ 0)
    (hu : DifferentiableAt ℝ u (Bracket.σ z)) (hv : DifferentiableAt ℝ v (Bracket.σ z)) :
    gradInner (u ∘ Bracket.σ) (v ∘ Bracket.σ) z =
      ((‖z‖⁻¹ ^ 4 : ℝ) : ℂ) * gradInner u v (Bracket.σ z) := by
  have hσ : DifferentiableAt ℝ Bracket.σ z :=
    (SigmaDeriv.hasFDerivAt_sigmaR hz).differentiableAt
  have hcu : fderiv ℝ (u ∘ Bracket.σ) z =
      (fderiv ℝ u (Bracket.σ z)).comp (fderiv ℝ Bracket.σ z) :=
    fderiv_comp z hu hσ
  have hcv : fderiv ℝ (v ∘ Bracket.σ) z =
      (fderiv ℝ v (Bracket.σ z)).comp (fderiv ℝ Bracket.σ z) :=
    fderiv_comp z hv hσ
  have hL1 : fderiv ℝ Bracket.σ z 1 = -(((starRingEnd ℂ) z) ^ 2)⁻¹ := by
    change fderiv ℝ (fun x : ℂ => 1 / (starRingEnd ℂ) x) z 1 = _
    rw [SigmaDeriv.fderiv_sigmaR_apply hz 1]
    simp
  have hLI : fderiv ℝ Bracket.σ z Complex.I =
      -(((starRingEnd ℂ) z) ^ 2)⁻¹ * -Complex.I := by
    change fderiv ℝ (fun x : ℂ => 1 / (starRingEnd ℂ) x) z Complex.I = _
    rw [SigmaDeriv.fderiv_sigmaR_apply hz Complex.I, Complex.conj_I]
  have hna : ‖-(((starRingEnd ℂ) z) ^ 2)⁻¹‖ ^ 2 = ‖z‖⁻¹ ^ 4 := by
    rw [norm_neg, norm_inv, norm_pow, Complex.norm_conj, ← inv_pow, ← pow_mul]
  unfold gradInner
  rw [hcu, hcv]
  simp only [ContinuousLinearMap.comp_apply]
  rw [hL1, hLI, mul_neg, ← hna]
  exact sesq_antilinear_weight (fderiv ℝ u (Bracket.σ z))
    (fderiv ℝ v (Bracket.σ z)) (-(((starRingEnd ℂ) z) ^ 2)⁻¹)

/-! ### The half annuli and the σ bijection between them -/

/-- The inner half-annulus `1/2 < ‖z‖ < 1`. -/
def innerHalfAnnulus : Set ℂ := {z | 1 / 2 < ‖z‖ ∧ ‖z‖ < 1}

/-- The outer half-annulus `1 < ‖w‖ < 2`. -/
def outerHalfAnnulus : Set ℂ := {z | 1 < ‖z‖ ∧ ‖z‖ < 2}

lemma isOpen_innerHalfAnnulus : IsOpen innerHalfAnnulus :=
  (isOpen_lt continuous_const continuous_norm).inter
    (isOpen_lt continuous_norm continuous_const)

lemma measurableSet_innerHalfAnnulus : MeasurableSet innerHalfAnnulus :=
  isOpen_innerHalfAnnulus.measurableSet

lemma innerHalfAnnulus_ne_zero {z : ℂ} (hz : z ∈ innerHalfAnnulus) : z ≠ 0 := by
  intro h
  have h1 := hz.1
  rw [h, norm_zero] at h1
  norm_num at h1

/-- σ is injective everywhere (a global involution, with the totalized value
`σ 0 = 0`). -/
lemma sigma_injOn (S : Set ℂ) : Set.InjOn Bracket.σ S :=
  fun x _ y _ h => by rw [← Bracket.σ_σ x, h, Bracket.σ_σ]

/-- σ carries the inner half-annulus onto the outer one. -/
lemma sigma_image_innerHalf :
    Bracket.σ '' innerHalfAnnulus = outerHalfAnnulus := by
  ext w
  constructor
  · rintro ⟨z, ⟨hz1, hz2⟩, rfl⟩
    have hz0 : (0 : ℝ) < ‖z‖ := lt_trans (by norm_num) hz1
    constructor
    · rw [Bracket.norm_σ]
      exact (one_lt_inv₀ hz0).mpr hz2
    · rw [Bracket.norm_σ, show (2 : ℝ) = (2⁻¹)⁻¹ by norm_num]
      exact (inv_lt_inv₀ hz0 (by norm_num)).mpr (by linarith)
  · intro hw
    obtain ⟨hw1, hw2⟩ := hw
    have hw0 : (0 : ℝ) < ‖w‖ := lt_trans (by norm_num) hw1
    refine ⟨Bracket.σ w, ⟨?_, ?_⟩, Bracket.σ_σ w⟩
    · rw [Bracket.norm_σ, show (1 : ℝ) / 2 = (2 : ℝ)⁻¹ by norm_num]
      exact (inv_lt_inv₀ (by norm_num) hw0).mpr hw2
    · rw [Bracket.norm_σ]
      exact (inv_lt_one₀ hw0).mpr hw1

lemma sigma_mem_outer {z : ℂ} (hz : z ∈ innerHalfAnnulus) :
    Bracket.σ z ∈ outerHalfAnnulus := by
  rw [← sigma_image_innerHalf]
  exact ⟨z, hz, rfl⟩

/-! ### The two transports -/

/-- The Dirichlet cross pairing transports
through the seam reflection with no extra factor: the `‖z‖⁻⁴` Jacobian weight
is exactly consumed by the sesquilinear pullback weight. -/
theorem gradInner_seam_transport {u v : ℂ → ℂ}
    (hu : ∀ w ∈ outerHalfAnnulus, DifferentiableAt ℝ u w)
    (hv : ∀ w ∈ outerHalfAnnulus, DifferentiableAt ℝ v w) :
    (∫ w in outerHalfAnnulus, gradInner u v w) =
      ∫ z in innerHalfAnnulus, gradInner (u ∘ Bracket.σ) (v ∘ Bracket.σ) z := by
  have hd : ∀ z ∈ innerHalfAnnulus,
      HasFDerivWithinAt Bracket.σ (fderiv ℝ Bracket.σ z) innerHalfAnnulus z :=
    fun z hz => ((SigmaDeriv.hasFDerivAt_sigmaR
      (innerHalfAnnulus_ne_zero hz)).differentiableAt.hasFDerivAt).hasFDerivWithinAt
  rw [← sigma_image_innerHalf,
    integral_image_eq_integral_abs_det_fderiv_smul volume
      measurableSet_innerHalfAnnulus hd (sigma_injOn _)]
  apply setIntegral_congr_fun measurableSet_innerHalfAnnulus
  intro z hz
  have hz0 : z ≠ 0 := innerHalfAnnulus_ne_zero hz
  have hσz : Bracket.σ z ∈ outerHalfAnnulus := sigma_mem_outer hz
  change |(fderiv ℝ Bracket.σ z).det| • gradInner u v (Bracket.σ z) =
    gradInner (u ∘ Bracket.σ) (v ∘ Bracket.σ) z
  rw [show |(fderiv ℝ Bracket.σ z).det| = ‖z‖⁻¹ ^ 4 from abs_det_sigma hz0,
    gradInner_comp_sigma hz0 (hu _ hσz) (hv _ hσz), Complex.real_smul]

/-- Inversion preserves the potential pairing for every k>=2.
No differentiability of the two functions is needed. -/
theorem potential_seam_transport_general (k : ℕ) (hk : 2 ≤ k) (u v : ℂ → ℂ) :
    (∫ w in outerHalfAnnulus, (potV k w : ℂ) * starRingEnd ℂ (u w) * v w) =
      ∫ z in innerHalfAnnulus, (potV k z : ℂ) *
        starRingEnd ℂ (u (Bracket.σ z)) * v (Bracket.σ z) := by
  have hd : ∀ z ∈ innerHalfAnnulus,
      HasFDerivWithinAt Bracket.σ (fderiv ℝ Bracket.σ z) innerHalfAnnulus z :=
    fun z hz => ((SigmaDeriv.hasFDerivAt_sigmaR
      (innerHalfAnnulus_ne_zero hz)).differentiableAt.hasFDerivAt).hasFDerivWithinAt
  rw [← sigma_image_innerHalf,
    integral_image_eq_integral_abs_det_fderiv_smul volume
      measurableSet_innerHalfAnnulus hd (sigma_injOn _)]
  apply setIntegral_congr_fun measurableSet_innerHalfAnnulus
  intro z hz
  have hz0 : z ≠ 0 := innerHalfAnnulus_ne_zero hz
  change |(fderiv ℝ Bracket.σ z).det| • ((potV k (Bracket.σ z) : ℂ) *
      starRingEnd ℂ (u (Bracket.σ z)) * v (Bracket.σ z)) =
    (potV k z : ℂ) * starRingEnd ℂ (u (Bracket.σ z)) * v (Bracket.σ z)
  rw [show |(fderiv ℝ Bracket.σ z).det| = ‖z‖⁻¹ ^ 4 from abs_det_sigma hz0,
    Complex.real_smul]
  have hV : ((‖z‖⁻¹ ^ 4 : ℝ) : ℂ) * (potV k (Bracket.σ z) : ℂ) = (potV k z : ℂ) := by
    have hr : ‖z‖⁻¹ ^ 4 * potV k (Bracket.σ z) = potV k z := by
      rw [Bracket.σ_apply, KsIndex.PotVSigma.potV_sigma k hk hz0]
      have hn : ‖z‖ ≠ 0 := norm_ne_zero_iff.mpr hz0
      field_simp
    exact_mod_cast hr
  calc ((‖z‖⁻¹ ^ 4 : ℝ) : ℂ) * ((potV k (Bracket.σ z) : ℂ) *
        starRingEnd ℂ (u (Bracket.σ z)) * v (Bracket.σ z))
      = (((‖z‖⁻¹ ^ 4 : ℝ) : ℂ) * (potV k (Bracket.σ z) : ℂ)) *
        starRingEnd ℂ (u (Bracket.σ z)) * v (Bracket.σ z) := by ring
    _ = (potV k z : ℂ) * starRingEnd ℂ (u (Bracket.σ z)) * v (Bracket.σ z) := by
        rw [hV]


theorem potential_seam_transport (u v : ℂ → ℂ) :
    (∫ w in outerHalfAnnulus, (potV 3 w : ℂ) * starRingEnd ℂ (u w) * v w) =
      ∫ z in innerHalfAnnulus, (potV 3 z : ℂ) *
        starRingEnd ℂ (u (Bracket.σ z)) * v (Bracket.σ z) :=
  potential_seam_transport_general 3 (by decide) u v

end KsIndex.Trace
