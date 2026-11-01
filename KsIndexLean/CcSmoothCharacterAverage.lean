module

public import KsIndexLean.CcSmoothRotationIntertwining
public import KsIndexLean.D5CharProjAlgebra

@[expose] public section


open Set Filter Topology
noncomputable section
namespace KsIndex.Trace
open KsIndex.FormIndex KsIndex.WeakH1

def ccSmoothCharacterAverage (k m : ℕ) (θ : ℝ)
    (hθ : Complex.exp (θ * Complex.I) ^ k = 1) (r : ℕ) :
    Module.End ℂ (KsIndex.Surface.CcSmooth k m) :=
  (k : ℂ)⁻¹ • ∑ i ∈ Finset.range k, xi k ^ (r * i) • ccSmoothRotation k m θ hθ ^ i

def chainChartCharacterAverage (k m : ℕ) [NeZero m] (θ : ℝ)
    (hθ : Complex.exp (θ * Complex.I) ^ k = 1) (r : ℕ) :
    Module.End ℂ (ChainChartSpace k m) :=
  (k : ℂ)⁻¹ • ∑ i ∈ Finset.range k,
    xi k ^ (r * i) • (chainChartRotationLI k m θ hθ).toLinearMap ^ i

lemma ccSmooth_character_average_intertwine (k m : ℕ) [NeZero m] (θ : ℝ)
    (hθ : Complex.exp (θ * Complex.I) ^ k = 1) (r : ℕ) (u : KsIndex.Surface.CcSmooth k m) :
    ccSmoothToChainChart k m (ccSmoothCharacterAverage k m θ hθ r u) =
      chainChartCharacterAverage k m θ hθ r (ccSmoothToChainChart k m u) := by
  simp only [ccSmoothCharacterAverage, chainChartCharacterAverage, LinearMap.smul_apply,
    LinearMap.sum_apply, map_smul, map_sum, ccSmoothToChainChart_rotation_pow]

lemma chainChartCharacterAverage_continuous (k m : ℕ) [NeZero m] (θ : ℝ)
    (hθ : Complex.exp (θ * Complex.I) ^ k = 1) (r : ℕ) :
    Continuous (chainChartCharacterAverage k m θ hθ r) := by
  have hp i : Continuous (fun q => ((chainChartRotationLI k m θ hθ).toLinearMap ^ i) q) := by
    induction i with
    | zero => exact continuous_id
    | succ i hi =>
      simpa only [pow_succ', Module.End.mul_apply, Function.comp_def,
        LinearIsometry.coe_toLinearMap] using (chainChartRotationLI k m θ hθ).continuous.comp hi
  simp only [chainChartCharacterAverage, LinearMap.coe_smul, LinearMap.coe_sum]
  convert (continuous_finsetSum (Finset.range k)
    (fun i _ => (hp i).const_smul (xi k ^ (r * i)))).const_smul ((k : ℂ)⁻¹) using 1
  ext q
  simp only [Pi.smul_apply, Finset.sum_apply]

/-- The finite average fixes every vector of its target character. -/
lemma chainChartCharacterAverage_fixed {k m : ℕ} (hk : 0 < k) [NeZero m] (θ : ℝ)
    (hθ : Complex.exp (θ * Complex.I) ^ k = 1) (r : ℕ) (q : ChainChartSpace k m)
    (hq : chainChartRotationLI k m θ hθ q = zeta k ^ r • q) :
    chainChartCharacterAverage k m θ hθ r q = q := by
  have hp i : ((chainChartRotationLI k m θ hθ).toLinearMap ^ i) q =
      (zeta k ^ r) ^ i • q := by
    induction i with
    | zero => simp
    | succ i hi =>
      simp only [pow_succ', Module.End.mul_apply, hi, map_smul]
      change (zeta k ^ r) ^ i • chainChartRotationLI k m θ hθ q = _
      rw [hq, smul_smul]
      congr 1
      ring
  have hterm i : xi k ^ (r * i) • ((chainChartRotationLI k m θ hθ).toLinearMap ^ i) q = q := by
    rw [hp, ← pow_mul, smul_smul, mul_comm, zeta_pow_mul_xi_pow hk, one_smul]
  simp only [chainChartCharacterAverage, LinearMap.smul_apply, LinearMap.sum_apply, hterm]
  rw [Finset.sum_const, Finset.card_range, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul,
    inv_mul_cancel₀ (Nat.cast_ne_zero.mpr hk.ne'), one_smul]

/-- Projecting original smooth approximants preserves convergence to a weak
vector already in the target character. Source membership is built into the
average's CcSmooth codomain. -/
theorem ccSmooth_character_average_tendsto {k m : ℕ} (hk : 0 < k) [NeZero m] (θ : ℝ)
    (hθ : Complex.exp (θ * Complex.I) ^ k = 1) (r : ℕ)
    (S : ℕ → KsIndex.Surface.CcSmooth k m) (q : ChainChartSpace k m)
    (ht : Tendsto (fun n => ccSmoothToChainChart k m (S n)) atTop (𝓝 q))
    (hq : chainChartRotationLI k m θ hθ q = zeta k ^ r • q) :
    Tendsto (fun n => ccSmoothToChainChart k m (ccSmoothCharacterAverage k m θ hθ r (S n)))
      atTop (𝓝 q) := by
  have h := ((chainChartCharacterAverage_continuous k m θ hθ r).tendsto q).comp ht
  rw [chainChartCharacterAverage_fixed hk θ hθ r q hq] at h
  simpa only [ccSmooth_character_average_intertwine, Function.comp_def] using h

/-- Every iterate, and hence the full finite character average, retains the
original pointwise translation phase. -/
lemma ccSmoothCharacterAverage_preserves_phase {k m : ℕ} (θ : ℝ)
    (hθ : Complex.exp (θ * Complex.I) ^ k = 1) (r : ℕ) (c : ℂ)
    (u : KsIndex.Surface.CcSmooth k m)
    (hu : ∀ n z, u.val (n + 2) z = c * u.val n z) :
    ∀ n z, (ccSmoothCharacterAverage k m θ hθ r u).val (n + 2) z =
      c * (ccSmoothCharacterAverage k m θ hθ r u).val n z := by
  have hp i : ∀ n z, ((ccSmoothRotation k m θ hθ ^ i) u).val (n + 2) z =
      c * ((ccSmoothRotation k m θ hθ ^ i) u).val n z := by
    induction i with
    | zero => exact hu
    | succ i hi =>
      simpa only [pow_succ', Module.End.mul_apply] using
        ccSmoothRotation_preserves_phase θ hθ c ((ccSmoothRotation k m θ hθ ^ i) u) hi
  intro n z
  simp only [ccSmoothCharacterAverage, LinearMap.smul_apply, LinearMap.sum_apply,
    Submodule.coe_smul, Submodule.coe_sum, Pi.smul_apply, Finset.sum_apply,
    smul_eq_mul, hp, Finset.mul_sum]
  congr 1
  funext i
  ring

lemma ccSmoothRotation_pow_uncurry {k m : ℕ} (θ : ℝ)
    (hθ : Complex.exp (θ * Complex.I) ^ k = 1) (i : ℕ)
    (u : KsIndex.Surface.CcSmooth k m) :
    KsIndex.Surface.uncurryE m (((ccSmoothRotation k m θ hθ ^ i) u).val) =
      (KsIndex.SurfaceSym.rotE m (Complex.exp (θ * Complex.I)) ^ i)
        (KsIndex.Surface.uncurryE m u.val) := by
  induction i with
  | zero => rfl
  | succ i hi =>
    simp only [pow_succ', Module.End.mul_apply]
    change KsIndex.SurfaceSym.rotE m (Complex.exp (θ * Complex.I))
      (KsIndex.Surface.uncurryE m (((ccSmoothRotation k m θ hθ ^ i) u).val)) = _
    rw [hi]

/-- The smooth average is precisely the existing finite character projection
on the original uncurried family, without identifying total representatives. -/
lemma ccSmoothCharacterAverage_uncurry {k m : ℕ} (θ : ℝ)
    (hθ : Complex.exp (θ * Complex.I) ^ k = 1) (r : ℕ)
    (u : KsIndex.Surface.CcSmooth k m) :
    KsIndex.Surface.uncurryE m (ccSmoothCharacterAverage k m θ hθ r u).val =
      charProj (KsIndex.SurfaceSym.rotE m (Complex.exp (θ * Complex.I))) k ⊤ r
        ⟨KsIndex.Surface.uncurryE m u.val, Submodule.mem_top⟩ := by
  simp only [ccSmoothCharacterAverage, charProj_apply, LinearMap.smul_apply,
    LinearMap.sum_apply, Submodule.coe_smul, Submodule.coe_sum, map_smul, map_sum,
    ccSmoothRotation_pow_uncurry]

/-- The average lands in the exact rotation eigenspace on original smooth
families; periodicity follows from the geometric root condition. -/
lemma ccSmoothCharacterAverage_mem_eigenspace {k m : ℕ} (hk : 0 < k) (θ : ℝ)
    (hθ : Complex.exp (θ * Complex.I) ^ k = 1) (r : ℕ)
    (u : KsIndex.Surface.CcSmooth k m) :
    KsIndex.Surface.uncurryE m (ccSmoothCharacterAverage k m θ hθ r u).val ∈
      Module.End.eigenspace (KsIndex.SurfaceSym.rotE m (Complex.exp (θ * Complex.I)))
        (zeta k ^ r) := by
  rw [ccSmoothCharacterAverage_uncurry]
  apply charProj_mem_eigenspace _ r hk
  · intro v hv
    funext p
    rw [KsIndex.SurfaceSym.rotE_pow_apply, hθ, one_mul]
  · intro v hv
    exact Submodule.mem_top

/-- Puncture-avoiding slit data in a weak rotation character admit original
smooth approximants with BOTH exact symmetries and convergence in chain H1. -/
theorem punctured_slit_smooth_joint_approximation {k m : ℕ} (hk : 1 ≤ k) [NeZero m]
    (c : ℂ) (hc : c ^ m = 1) (p : slitTraceDomain k c)
    (θ : ℝ) (hθ : Complex.exp (θ * Complex.I) ^ k = 1) (r : ℕ)
    (hq : chainChartRotationLI k m θ hθ (reconstructChainPhase k m c hc p).val =
      zeta k ^ r • (reconstructChainPhase k m c hc p).val)
    {H : Set ℂ} (hH : IsOpen H) (hpH : KsIndex.Surface.punctures k ⊆ H)
    (hu : ∀ᵐ z ∂MeasureTheory.volume.restrict (disk : Set ℂ),
      z ∈ H → KsIndex.WeakH1.valueCLM p.val.1 z = 0)
    (hv : ∀ᵐ z ∂MeasureTheory.volume.restrict (disk : Set ℂ),
      z ∈ H → KsIndex.WeakH1.valueCLM p.val.2 z = 0) :
    ∃ S : ℕ → KsIndex.Surface.CcSmooth k m,
      (∀ i n z, (S i).val (n + 2) z = c * (S i).val n z) ∧
      (∀ i, KsIndex.Surface.uncurryE m (S i).val ∈
        Module.End.eigenspace (KsIndex.SurfaceSym.rotE m (Complex.exp (θ * Complex.I)))
          (zeta k ^ r)) ∧
      Tendsto (fun i => ccSmoothToChainChart k m (S i)) atTop
        (𝓝 (reconstructChainPhase k m c hc p).val) := by
  obtain ⟨S, hphase, ht⟩ :=
    punctured_slit_smooth_chain_approximation hk c hc p hH hpH hu hv
  refine ⟨fun i => ccSmoothCharacterAverage k m θ hθ r (S i), ?_, ?_, ?_⟩
  · intro i
    exact ccSmoothCharacterAverage_preserves_phase θ hθ r c (S i) (hphase i)
  · intro i
    exact ccSmoothCharacterAverage_mem_eigenspace hk θ hθ r (S i)
  · exact ccSmooth_character_average_tendsto hk θ hθ r S _ ht hq

end KsIndex.Trace
