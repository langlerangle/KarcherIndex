module

public import KsIndexLean.ExplicitModeJacobi
public import KsIndexLean.DtNCircle
public import KsIndexLean.NeumannKernelClassification

@[expose] public section


noncomputable section
open Set MeasureTheory
namespace KsIndex.Trace
open KsIndex.WeakH1 KsIndex.JacobiMode KsIndex.Radial KsIndex.DtNCircle

/-- The explicit signed mode has boundary amplitude |n|, including zero at n=0. -/
lemma signedModeU_boundary (k : ℕ) (n : ℤ) (w : Circle₁) :
    signedModeU k n w = (n.natAbs : ℂ) * fourierAmbient n w := by
  have hw : ‖(w : ℂ)‖ = 1 := mem_sphere_zero_iff_norm.mp w.property
  have hg (m : ℕ) : (gRad k m 1 : ℂ) = (m : ℂ) := by
    simp only [gRad, one_pow, mul_one]
    push_cast
    ring
  cases n with
  | ofNat m => simp [signedModeU, modeU, hw, hg, fourierAmbient]
  | negSucc m => simp [signedModeU, modeU, hw, hg, fourierAmbient, map_mul, map_pow]

/-- Boundary-normalized smooth Jacobi mode as an actual weak H1 element. -/
def normalizedJacobiMode {k : ℕ} (hk : 2 ≤ k) (n : NZ) : ComplexH1 :=
  (n.val.natAbs : ℂ)⁻¹ • globalSmoothH1 (signedModeU k n) (signedModeU_smooth hk n)

lemma normalizedJacobiMode_trace {k : ℕ} (hk : 2 ≤ k) (n : NZ) :
    diskTraceCLM (normalizedJacobiMode hk n) = fourierTestLp n := by
  have hn : (n.val.natAbs : ℂ) ≠ 0 := by exact_mod_cast Int.natAbs_ne_zero.mpr n.property
  rw [normalizedJacobiMode, map_smul]
  apply Lp.ext
  filter_upwards [Lp.coeFn_smul (n.val.natAbs : ℂ)⁻¹
      (diskTraceCLM (globalSmoothH1 (signedModeU k n) (signedModeU_smooth hk n))),
    globalSmoothH1_trace (signedModeU k n) (signedModeU_smooth hk n),
    fourierTestLp_coe n] with w hs ht hf
  simp only [hs, Pi.smul_apply, smul_eq_mul, ht, signedModeU_boundary, hf]
  exact inv_mul_cancel_left₀ hn _

lemma normalizedJacobiMode_symbol (k : ℕ) (n : NZ) :
    (n.val.natAbs : ℂ)⁻¹ * (((n.val.natAbs : ℝ) ^ 2 - kap k ^ 2 : ℝ) : ℂ) =
      (dtnSymbol k n : ℂ) := by
  obtain ⟨n, hn⟩ := n
  cases n with
  | ofNat m =>
    change (m : ℂ)⁻¹ * (((m : ℝ) ^ 2 - kap k ^ 2 : ℝ) : ℂ) =
      ((((m : ℝ) ^ 2 - kap k ^ 2) / |(m : ℝ)| : ℝ) : ℂ)
    rw [abs_of_nonneg (Nat.cast_nonneg m)]
    push_cast
    ring
  | negSucc m =>
    simp only [Int.natAbs_negSucc, dtnSymbol, Int.cast_negSucc, kap]
    rw [abs_neg, abs_of_nonneg (Nat.cast_nonneg (m + 1)), neg_sq]
    push_cast
    ring

/-- The classical normal derivative divided by the boundary amplitude is the DtN symbol. -/
lemma signedModeU_normal_normalized {k : ℕ} (hk : 2 ≤ k) (n : NZ) (w : Circle₁) :
    (n.val.natAbs : ℂ)⁻¹ * fderiv ℝ (signedModeU k n) w w =
      (dtnSymbol k n : ℂ) * fourierAmbient n w := by
  rw [signedModeU_normal hk, ← mul_assoc, normalizedJacobiMode_symbol]

/-- Unrestricted weak Green identity, with the actual normalized Fourier normal flux. -/
lemma normalizedJacobiMode_weak_green {k : ℕ} (hk : 2 ≤ k) (n : NZ) (v : ComplexH1) :
    weakJacobi (surfacePotential k) (normalizedJacobiMode hk n) v =
      inner ℂ ((dtnSymbol k n : ℂ) • fourierTestLp n) (diskTraceCLM v) := by
  let a : ℂ := (((n.val.natAbs : ℝ) ^ 2 - kap k ^ 2 : ℝ) : ℂ)
  have hF : ((a • fourierTestLp n : Lp ℂ 2 circleMeasure) : Circle₁ → ℂ)
      =ᵐ[circleMeasure] fun w => fderiv ℝ (signedModeU k n) w w := by
    filter_upwards [Lp.coeFn_smul a (fourierTestLp n), fourierTestLp_coe n] with w hw hf
    simp only [hw, Pi.smul_apply, smul_eq_mul, hf, signedModeU_normal hk]
    rfl
  have hg := smooth_weak_green_of_flux (surfacePotential k) (signedModeU k n)
    (signedModeU_smooth hk n) (fun w _ => signedModeU_jacobi hk n w)
    (a • fourierTestLp n) hF v
  have ha : (n.val.natAbs : ℂ)⁻¹ * a = (dtnSymbol k n : ℂ) :=
    normalizedJacobiMode_symbol k n
  rw [normalizedJacobiMode, weakJacobi_smul_left, hg, ← inner_smul_left,
    smul_smul, ha]

/-- Every normalized mode solves the weak Jacobi equation against all zero-trace tests. -/
lemma normalizedJacobiMode_weak_zeroTrace {k : ℕ} (hk : 2 ≤ k) (n : NZ)
    (v : ComplexH1) (hv : v ∈ zeroTraceDomain Set.univ) :
    weakJacobi (surfacePotential k) (normalizedJacobiMode hk n) v = 0 := by
  have ht := (mem_zeroTraceDomain Set.univ v).mp hv
  rw [Measure.restrict_univ] at ht
  have hz : diskTraceCLM v = 0 := by
    apply Lp.ext
    filter_upwards [ht,
      Lp.coeFn_zero (E := ℂ) (p := (2 : ENNReal)) (μ := circleMeasure)] with w hw h0
    exact hw.trans h0.symm
  rw [normalizedJacobiMode_weak_green, hz, inner_zero_right]

/-- Exact signed-mode pairing, retaining the geometric 2π factor. -/
lemma normalizedJacobiMode_pairing {k : ℕ} (hk : 2 ≤ k) (n m : NZ) :
    weakJacobi (surfacePotential k) (normalizedJacobiMode hk n)
      (normalizedJacobiMode hk m) =
      (2 * Real.pi : ℂ) * (dtnSymbol k n : ℂ) * (Pi.single m.val 1 : ℤ → ℂ) n.val := by
  rw [normalizedJacobiMode_weak_green, normalizedJacobiMode_trace,
    inner_smul_left, fourierTestLp_inner_unscaled]
  have hc : circleFourierCoeff (fourierTestLp m) n = (Pi.single m.val 1 : ℤ → ℂ) n.val := by
    rw [congrFun (circleFourierCoeff_congr_ae (fourierTestLp_coe m)) n]
    exact circleFourierCoeff_fourierAmbient m n
  rw [hc, Complex.conj_ofReal]
  push_cast
  ring

end KsIndex.Trace
