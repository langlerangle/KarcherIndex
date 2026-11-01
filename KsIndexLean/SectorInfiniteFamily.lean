module

public import KsIndexLean.CompactPolarTests
public import KsIndexLean.NaturalCoreCharacter
public import KsIndexLean.WeakBoundaryDomains
public import KsIndexLean.DiskH1RotationIsometry
public import KsIndexLean.PlaneRotation
public import Mathlib.LinearAlgebra.Eigenspace.Basic
public import Mathlib.Analysis.Real.Pi.Irrational

@[expose] public section


/-!
# Infinite-dimensional mixed character sectors

For `k > 0`, every natural character index `r` and every pair of boundary flags,
we exhibit an explicit `ℕ`-indexed family in `mixedCharacterDomain k r b₁ b₀`
and show it is linearly independent, hence the sector is not finite-dimensional.

**Construction**: a single smooth radial cutoff `χ`
(supported in the annulus `1/4 < ‖z‖ < 3/4`, with `χ (1/2) = 1`) times the ambient angular
mode `fourierAmbient nₘ` evaluated at `nUnit z`, where `nₘ = k·m − r`. Each member:
* lies in `H¹` and has **zero trace on every arc** (`compactPolarTestH1_zeroTrace`), so it lies
  in `mixedTraceDomain k b₁ b₀` for *any* flag pair;
* satisfies the sector character equation `diskRotation (−2π/k) u = ζ_k^r • u`
  (`weakCharacter_of_value_eq`), because `nₘ ≡ −r (mod k)`.

**Independence**: each member is an eigenvector of the *single* operator `diskRotation 1`, with
eigenvalue `exp (nₘ · I)`.  These eigenvalues are distinct because the `nₘ = k·m − r` are distinct
and `2π` is irrational (`irrational_pi`), so `Module.End.eigenvectors_linearIndependent'` gives an
infinite linearly independent family, whence `¬ FiniteDimensional`.
-/

noncomputable section
open MeasureTheory Complex Set
open scoped ContDiff Real
namespace KsIndex.Trace
open KsIndex.WeakH1

/-! ### The fixed radial cutoff and the family -/

/-- A smooth radial bump centred at `1/2`, supported in `(3/8, 5/8) ⊆ (1/4, 3/4)`, equal to `1`
at `1/2`. -/
def sectorBump : ContDiffBump (1 / 2 : ℝ) := ⟨1 / 16, 1 / 8, by norm_num, by norm_num⟩

lemma sectorBump_contDiff : ContDiff ℝ (⊤ : ℕ∞) (sectorBump : ℝ → ℝ) := sectorBump.contDiff

lemma sectorBump_tsupport : tsupport (sectorBump : ℝ → ℝ) ⊆ Ioo (1 / 4 : ℝ) (3 / 4) := by
  rw [sectorBump.tsupport_eq]
  intro x hx
  rw [Metric.mem_closedBall, Real.dist_eq, abs_le] at hx
  exact ⟨by simp only [sectorBump] at hx ⊢; linarith [hx.1], by
    simp only [sectorBump] at hx ⊢; linarith [hx.2]⟩

lemma sectorBump_one : (sectorBump : ℝ → ℝ) (1 / 2) = 1 := by
  apply sectorBump.one_of_mem_closedBall
  simp [Metric.mem_closedBall, sectorBump]

/-- Angular frequency of member `m` for character class `r`: chosen `≡ −r (mod k)`. -/
def sectorFreq (k r m : ℕ) : ℤ := (k : ℤ) * m - r

/-- The explicit `H¹` family inside the sector. -/
def sectorFamily (k r m : ℕ) : ComplexH1 :=
  compactPolarTestH1 (show (0 : ℝ) < 1 / 4 by norm_num) sectorBump_contDiff sectorBump_tsupport
    (sectorFreq k r m)

lemma sectorFamily_value (k r m : ℕ) :
    valueCLM (sectorFamily k r m) =ᵐ[volume.restrict (disk : Set ℂ)]
      compactPolarTest (sectorBump : ℝ → ℝ) (sectorFreq k r m) := by
  unfold sectorFamily compactPolarTestH1
  exact globalSmoothH1_value _ _

/-! ### The rotation identity -/

lemma fourierAmbient_one (n : ℤ) : fourierAmbient n 1 = 1 := by
  cases n <;> simp [fourierAmbient]

/-- The ambient Fourier modes rotate by a pure phase. -/
lemma fourierAmbient_planeRotation (n : ℤ) (θ : ℝ) (w : ℂ) :
    fourierAmbient n (planeRotation θ w) = Complex.exp ((n : ℂ) * θ * I) * fourierAmbient n w := by
  rw [planeRotation_apply]
  cases n with
  | ofNat p =>
    have hp : Complex.exp ((θ : ℂ) * I) ^ p = Complex.exp ((p : ℂ) * θ * I) := by
      rw [← Complex.exp_nat_mul]; congr 1; ring
    simp only [fourierAmbient, Int.ofNat_eq_natCast, Int.cast_natCast, mul_pow, hp]
  | negSucc p =>
    have hc : (starRingEnd ℂ) (Complex.exp ((θ : ℂ) * I)) = Complex.exp (-((θ : ℂ) * I)) := by
      rw [← Complex.exp_conj]; congr 1
      rw [map_mul, Complex.conj_ofReal, Complex.conj_I]; ring
    have hpow : ((starRingEnd ℂ) (Complex.exp ((θ : ℂ) * I))) ^ (p + 1)
        = Complex.exp ((Int.negSucc p : ℂ) * θ * I) := by
      rw [hc, ← Complex.exp_nat_mul]; congr 1
      push_cast [Int.negSucc_eq]; ring
    simp only [fourierAmbient, map_mul, mul_pow, hpow]

/-- Same phase identity, lifted to the compactly-supported test functions. -/
lemma compactPolarTest_planeRotation (χ : ℝ → ℝ) (n : ℤ) (θ : ℝ) (z : ℂ) :
    compactPolarTest χ n (planeRotation θ z)
      = Complex.exp ((n : ℂ) * θ * I) * compactPolarTest χ n z := by
  have hnorm : ‖planeRotation θ z‖ = ‖z‖ := (planeRotation θ).norm_map z
  have hunit : nUnit (planeRotation θ z) = planeRotation θ (nUnit z) := by
    rw [nUnit, nUnit, hnorm, planeRotation_apply, planeRotation_apply,
      Complex.real_smul, Complex.real_smul]
    ring
  simp only [compactPolarTest, hnorm, hunit, fourierAmbient_planeRotation]; ring

/-! ### Membership in the sector -/

lemma sectorFamily_mem_naturalArc (k r m n : ℕ) (b : Bool) :
    sectorFamily k r m ∈ naturalArcDomain k n b := by
  cases b
  · change sectorFamily k r m ∈ zeroTraceDomain (boundaryArc k n)
    exact compactPolarTestH1_zeroTrace (show (0 : ℝ) < 1 / 4 by norm_num) (by norm_num)
      sectorBump_contDiff sectorBump_tsupport (sectorFreq k r m) (boundaryArc k n)
  · exact Submodule.mem_top

lemma sectorFamily_char_mem (k r m : ℕ) (hk : 0 < k) :
    sectorFamily k r m ∈
      weakCharacterDomain (-(2 * Real.pi) / k) (KsIndex.FormIndex.zeta k ^ r) := by
  apply weakCharacter_of_value_eq _ _ _ (sectorFamily_value k r m)
  intro z
  rw [compactPolarTest_planeRotation]
  congr 1
  have hk' : (k : ℂ) ≠ 0 := by exact_mod_cast hk.ne'
  rw [KsIndex.FormIndex.zeta, ← Complex.exp_nat_mul]
  refine Complex.exp_eq_exp_iff_exists_int.mpr ⟨-(m : ℤ), ?_⟩
  simp only [sectorFreq]
  push_cast
  field_simp
  ring

lemma sectorFamily_mem (k r m : ℕ) (hk : 0 < k) (b₁ b₀ : Bool) :
    sectorFamily k r m ∈ mixedCharacterDomain k r b₁ b₀ :=
  ⟨⟨sectorFamily_mem_naturalArc k r m 1 b₁, sectorFamily_mem_naturalArc k r m 0 b₀⟩,
    sectorFamily_char_mem k r m hk⟩

/-! ### Nonvanishing -/

lemma sectorFamily_ne_zero (k r m : ℕ) : sectorFamily k r m ≠ 0 := by
  intro h
  have hn : ‖(1 : ℂ) / 2‖ = 1 / 2 := by
    rw [show ((1 : ℂ) / 2) = ((1 / 2 : ℝ) : ℂ) by norm_num, Complex.norm_real]; norm_num
  have h0 : valueCLM (sectorFamily k r m) =ᵐ[volume.restrict (disk : Set ℂ)] (0 : ℂ → ℂ) := by
    rw [h, map_zero]; exact Lp.coeFn_zero ℂ 2 _
  have hae : compactPolarTest (sectorBump : ℝ → ℝ) (sectorFreq k r m)
      =ᵐ[volume.restrict (disk : Set ℂ)] 0 := (sectorFamily_value k r m).symm.trans h0
  have hcont : Continuous (compactPolarTest (sectorBump : ℝ → ℝ) (sectorFreq k r m)) :=
    (compactPolarTest_smooth (show (0 : ℝ) < 1 / 4 by norm_num) sectorBump_contDiff
      sectorBump_tsupport _).continuous
  have hset : (disk : Set ℂ) = Metric.ball (0 : ℂ) 1 := rfl
  have heq : EqOn (compactPolarTest (sectorBump : ℝ → ℝ) (sectorFreq k r m)) 0 (disk : Set ℂ) := by
    rw [hset] at hae ⊢
    exact Measure.eqOn_open_of_ae_eq hae Metric.isOpen_ball hcont.continuousOn continuousOn_const
  have hmem : ((1 : ℂ) / 2) ∈ (disk : Set ℂ) := by
    rw [hset, Metric.mem_ball, dist_zero_right, hn]; norm_num
  have hval : compactPolarTest (sectorBump : ℝ → ℝ) (sectorFreq k r m) ((1 : ℂ) / 2) = 1 := by
    have hu : nUnit ((1 : ℂ) / 2) = 1 := by rw [nUnit, hn, Complex.real_smul]; norm_num
    simp only [compactPolarTest, hn, hu, fourierAmbient_one, mul_one, sectorBump_one,
      Complex.ofReal_one]
  have hz := heq hmem
  rw [hval] at hz
  exact one_ne_zero hz

/-! ### The eigenvector structure and independence -/

/-- Eigenvalue of member `m` under `diskRotation 1`. -/
def sectorEig (k r m : ℕ) : ℂ := Complex.exp ((sectorFreq k r m : ℂ) * I)

lemma sectorFamily_hasEigenvector (k r m : ℕ) :
    Module.End.HasEigenvector ((diskRotation 1).toLinearMap) (sectorEig k r m)
      (sectorFamily k r m) := by
  refine ⟨Module.End.mem_eigenspace_iff.mpr ?_, sectorFamily_ne_zero k r m⟩
  have hmem : sectorFamily k r m ∈ weakCharacterDomain (1 : ℝ) (sectorEig k r m) := by
    apply weakCharacter_of_value_eq _ _ _ (sectorFamily_value k r m)
    intro z
    rw [compactPolarTest_planeRotation]
    congr 1
    simp only [sectorEig]; congr 1; push_cast; ring
  have hrot := (mem_weakCharacterDomain 1 (sectorEig k r m) (sectorFamily k r m)).mp hmem
  simpa using hrot

lemma sectorEig_injective (k r : ℕ) (hk : 0 < k) : Function.Injective (sectorEig k r) := by
  intro m₁ m₂ h
  simp only [sectorEig] at h
  rw [Complex.exp_eq_exp_iff_exists_int] at h
  obtain ⟨t, ht⟩ := h
  have hcancel : (sectorFreq k r m₁ : ℂ) = (sectorFreq k r m₂ : ℂ) + (t : ℂ) * (2 * (π : ℂ)) := by
    have heq : (sectorFreq k r m₁ : ℂ) * I
        = ((sectorFreq k r m₂ : ℂ) + (t : ℂ) * (2 * (π : ℂ))) * I := by rw [ht]; ring
    exact mul_right_cancel₀ Complex.I_ne_zero heq
  have hR : (sectorFreq k r m₁ : ℝ) = (sectorFreq k r m₂ : ℝ) + (t : ℝ) * (2 * π) := by
    have h' : ((sectorFreq k r m₁ : ℝ) : ℂ)
        = (((sectorFreq k r m₂ : ℝ) + (t : ℝ) * (2 * π)) : ℂ) := by
      push_cast; linear_combination hcancel
    exact_mod_cast h'
  rcases eq_or_ne t 0 with ht0 | ht0
  · subst ht0
    simp only [Int.cast_zero, zero_mul, add_zero] at hR
    have : sectorFreq k r m₁ = sectorFreq k r m₂ := by exact_mod_cast hR
    have hk' : (k : ℤ) ≠ 0 := by exact_mod_cast hk.ne'
    simp only [sectorFreq] at this
    exact_mod_cast (mul_left_cancel₀ hk' (by linarith [this] : (k : ℤ) * m₁ = (k : ℤ) * m₂))
  · have h2t : (2 * t : ℤ) ≠ 0 := by omega
    have h2t' : ((2 * t : ℤ) : ℝ) ≠ 0 := by exact_mod_cast h2t
    have hpi : (π : ℝ)
        = ((sectorFreq k r m₁ - sectorFreq k r m₂ : ℤ) : ℝ) / ((2 * t : ℤ) : ℝ) := by
      rw [eq_div_iff h2t']
      push_cast
      linear_combination -hR
    exact absurd hpi (irrational_pi.ne_rational _ _)

/-! ### The conclusion -/

theorem mixedCharacterDomain_not_finiteDimensional (k r : ℕ) (hk : 0 < k) (b₁ b₀ : Bool) :
    ¬ FiniteDimensional ℂ (mixedCharacterDomain k r b₁ b₀) := by
  intro hfd
  set S := mixedCharacterDomain k r b₁ b₀ with hS
  have hLI_amb : LinearIndependent ℂ (fun m : ℕ => sectorFamily k r m) :=
    Module.End.eigenvectors_linearIndependent' ((diskRotation (1 : ℝ)).toLinearMap)
      (sectorEig k r) (sectorEig_injective k r hk)
      (fun m => sectorFamily k r m) (fun m => sectorFamily_hasEigenvector k r m)
  let v : ℕ → S := fun m => ⟨sectorFamily k r m, sectorFamily_mem k r m hk b₁ b₀⟩
  have hLI : LinearIndependent ℂ v := LinearIndependent.of_comp (Submodule.subtype S) hLI_amb
  have : Finite ℕ := Cardinal.lt_aleph0_iff_finite.mp hLI.lt_aleph0_of_finiteDimensional
  exact not_finite ℕ

end KsIndex.Trace
