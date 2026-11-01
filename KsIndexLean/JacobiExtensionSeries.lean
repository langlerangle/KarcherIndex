module

public import KsIndexLean.FiniteJacobiExtensionBound
public import KsIndexLean.DNHalfTraceSpace
public import Mathlib.Analysis.InnerProductSpace.Subspace

@[expose] public section


noncomputable section
open Set Filter MeasureTheory
open scoped Topology
namespace KsIndex.Trace
open KsIndex.WeakH1 KsIndex.DtNCircle KsIndex.CircleSobolev

private lemma summable_of_orthogonal_sq {ι : Type*} (v : ι → ComplexH1)
    (ho : Pairwise fun i j => inner ℂ (v i) (v j) = 0)
    (hs : Summable fun i => ‖v i‖ ^ 2) : Summable v := by
  let G (i : ι) := Submodule.span ℂ {v i}
  have hG : OrthogonalFamily ℂ (fun i => G i) (fun i => (G i).subtypeₗᵢ) := by
    intro i j hij x y
    obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp x.property
    obtain ⟨b, hb⟩ := Submodule.mem_span_singleton.mp y.property
    change inner ℂ x.val y.val = 0
    rw [← ha, ← hb, inner_smul_left, inner_smul_right, ho hij, mul_zero, mul_zero]
  let f (i : ι) : G i := ⟨v i, Submodule.subset_span (by simp)⟩
  exact (hG.summable_iff_norm_sq_summable f).mpr hs

lemma half_coeff_weight_summable (f : Space (1 / 2 : ℝ)) :
    Summable (fun n : ℤ => (1 + |(n : ℝ)|) * ‖coeff (1 / 2 : ℝ) f n‖ ^ 2) := by
  have h := (hasSum_weighted_sq (1 / 2 : ℝ) f).summable
  simpa only [weight_sq, show (2 : ℝ) * (1 / 2) = 1 by norm_num, Real.rpow_one] using h

/-- The actual H1 mode series is summable for every half-order physical coefficient family. -/
lemma jacobiExtension_summable {k : ℕ} (hk : 2 ≤ k) (f : Space (1 / 2 : ℝ)) :
    Summable (fun n : NZ => coeff (1 / 2 : ℝ) f n • normalizedJacobiMode hk n) := by
  apply summable_of_orthogonal_sq
  · intro n m hnm
    rw [inner_smul_left, inner_smul_right, normalizedJacobiMode_inner_eq_zero hk n m hnm,
      mul_zero, mul_zero]
  · apply Summable.of_nonneg_of_le (fun n => sq_nonneg _) _
      (((half_coeff_weight_summable f).subtype (fun n => n ≠ 0)).mul_left (jacobiModeH1Constant k))
    intro n
    rw [norm_smul, mul_pow]
    have h := mul_le_mul_of_nonneg_left (normalizedJacobiMode_norm_sq_le hk n)
      (sq_nonneg ‖coeff (1 / 2 : ℝ) f n‖)
    dsimp only [Function.comp_apply]
    nlinarith

/-- Extension by the convergent signed Jacobi series; zero frequency is omitted. -/
def jacobiExtensionH1 {k : ℕ} (hk : 2 ≤ k) (f : Space (1 / 2 : ℝ)) : ComplexH1 :=
  ∑' n : NZ, coeff (1 / 2 : ℝ) f n • normalizedJacobiMode hk n

lemma hasSum_jacobiExtension {k : ℕ} (hk : 2 ≤ k) (f : Space (1 / 2 : ℝ)) :
    HasSum (fun n : NZ => coeff (1 / 2 : ℝ) f n • normalizedJacobiMode hk n)
      (jacobiExtensionH1 hk f) := (jacobiExtension_summable hk f).hasSum

lemma jacobiExtensionH1_add {k : ℕ} (hk : 2 ≤ k) (f g : Space (1 / 2 : ℝ)) :
    jacobiExtensionH1 hk (f + g) = jacobiExtensionH1 hk f + jacobiExtensionH1 hk g := by
  unfold jacobiExtensionH1
  simp only [show ∀ n, coeff (1 / 2 : ℝ) (f + g) n =
    coeff (1 / 2 : ℝ) f n + coeff (1 / 2 : ℝ) g n from fun n => (coeffLinear _ n).map_add f g,
    add_smul]
  exact (jacobiExtension_summable hk f).tsum_add (jacobiExtension_summable hk g)

lemma jacobiExtensionH1_smul {k : ℕ} (hk : 2 ≤ k) (c : ℂ) (f : Space (1 / 2 : ℝ)) :
    jacobiExtensionH1 hk (c • f) = c • jacobiExtensionH1 hk f := by
  unfold jacobiExtensionH1
  simp only [show ∀ n, coeff (1 / 2 : ℝ) (c • f) n = c • coeff (1 / 2 : ℝ) f n
    from fun n => (coeffLinear _ n).map_smul c f, smul_eq_mul, mul_smul]
  exact (jacobiExtension_summable hk f).tsum_const_smul c

/-- The Jacobi equation passes to all half-order data by H1 convergence. -/
lemma jacobiExtensionH1_weak_zeroTrace {k : ℕ} (hk : 2 ≤ k) (f : Space (1 / 2 : ℝ))
    (v : ComplexH1) (hv : v ∈ zeroTraceDomain Set.univ) :
    weakJacobi (surfacePotential k) (jacobiExtensionH1 hk f) v = 0 := by
  have hc : Continuous (fun u : ComplexH1 => weakJacobi (surfacePotential k) u v) :=
    by simpa only [Function.comp_def, weakJacobi_conj] using
      Complex.continuous_conj.comp (continuous_weakJacobi_fixed_left (surfacePotential k) v)
  have ht := hc.continuousAt.tendsto.comp (hasSum_jacobiExtension hk f)
  have he : (fun s : Finset NZ => weakJacobi (surfacePotential k)
      (∑ n ∈ s, coeff (1 / 2 : ℝ) f n • normalizedJacobiMode hk n) v) = fun _ => 0 := by
    funext s
    exact finiteJacobiExtension_weak_zeroTrace hk s _ v hv
  change Tendsto (fun s : Finset NZ => weakJacobi (surfacePotential k)
    (∑ n ∈ s, coeff (1 / 2 : ℝ) f n • normalizedJacobiMode hk n) v) atTop _ at ht
  rw [he] at ht
  exact (tendsto_nhds_unique ht tendsto_const_nhds)

end KsIndex.Trace
