module

public import KsIndexLean.KarcherInfinityPrimitive
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.Normed.Module.Connected
public import Mathlib.Analysis.Normed.Module.Ball.Pointwise
public import Mathlib.Topology.LocallyConstant.Basic

@[expose] public section


/-! Identification of infinity primitives with the actual quotient integral. -/
noncomputable section
open Set Metric
open scoped Topology Pointwise ContDiff
namespace KsIndex.KarcherData

lemma projectPeriod_sub (p q : ℝ × ℝ × ℝ) :
    projectPeriod (p - q) = projectPeriod p - projectPeriod q := by
  simp [projectPeriod]

/-- Parameter overlap, excluding the regular infinity point itself. -/
def infinityOverlap (r : ℝ) : Set ℂ := {v | v ≠ 0 ∧ ‖v‖ < r}

lemma isOpen_infinityOverlap (r : ℝ) : IsOpen (infinityOverlap r) :=
  isOpen_ne.inter (isOpen_lt continuous_norm continuous_const)

lemma inv_not_puncture_of_norm_lt_one {k : ℕ} (hk : 2 ≤ k) {v : ℂ}
    (hv : ‖v‖ < 1) : v⁻¹ ∉ Surface.punctures k := by
  intro hp
  have he := puncture_norm hk hp
  rw [norm_inv, inv_eq_one] at he
  exact (ne_of_lt hv) he

/-- The finite-chart point corresponding to an overlap parameter. -/
def infinityOverlapPoint {k : ℕ} (hk : 2 ≤ k) {r : ℝ} (hr : r ≤ 1)
    (v : infinityOverlap r) : PuncturedPlane k :=
  ⟨v.val⁻¹, inv_not_puncture_of_norm_lt_one hk (v.property.2.trans_le hr)⟩

lemma isPreconnected_infinityOverlap (r : ℝ) : IsPreconnected (infinityOverlap r) := by
  have hs := isPreconnected_sphere
    (by simp [Complex.rank_real_complex] : 1 < Module.rank ℝ ℂ) (0 : ℂ) 1
  have hI : IsPreconnected (Ioo (0 : ℝ) r) := isPreconnected_Ioo
  have hp := hI.prod hs
  have hi := hp.image (fun p : ℝ × ℂ => p.1 • p.2)
    (continuous_fst.smul continuous_snd).continuousOn
  rw [Set.image_prod] at hi
  change IsPreconnected (Ioo (0 : ℝ) r • sphere (0 : ℂ) 1) at hi
  rw [Ioo_smul_sphere_zero (le_refl 0) (by norm_num : (0 : ℝ) < 1)] at hi
  convert hi using 1
  ext v
  simp [infinityOverlap, mul_one, mem_ball, dist_zero_right, and_comm]

/-- Locally, the difference between the actual quotient map and any primitive
with the prescribed infinity differential is constant. -/
theorem infinity_difference_locally_constant {k : ℕ} (hk : 2 ≤ k)
    (b : PuncturedPlane k) {r : ℝ} (hr : r ≤ 1) (X : ℂ → ℝ × ℝ × ℝ)
    (hX : ∀ v ∈ ball (0 : ℂ) r, HasFDerivAt X (infinityRealDifferential k v) v) :
    IsLocallyConstant (fun v : infinityOverlap r =>
      descendedIntegral hk b (infinityOverlapPoint hk hr v) - projectPeriod (X v.val)) := by
  apply (IsLocallyConstant.iff_eventually_eq _).mpr
  intro x
  let wx := infinityOverlapPoint hk hr x
  obtain ⟨s, hs, F₁, F₂, F₃, hF₁, hF₂, hF₃, hd₁, hd₂, hd₃, hrepr⟩ :=
    exists_local_primitives hk b wx
  let Y : ℂ → ℝ × ℝ × ℝ := fun v => realPrimitive F₁ F₂ F₃ v⁻¹
  have hYx : Y x.val = 0 := by
    simpa [Y, realPrimitive, wx, infinityOverlapPoint] using
      show ((F₁ wx.val).re, (F₂ wx.val).re, (F₃ wx.val).re) = (0 : ℝ × ℝ × ℝ) by
        simp [hF₁, hF₂, hF₃]
  have hn : {v : ℂ | v ∈ infinityOverlap r ∧ v⁻¹ ∈ ball wx.val s} ∈ 𝓝 x.val :=
    Filter.inter_mem ((isOpen_infinityOverlap r).mem_nhds x.property)
      ((continuousAt_inv₀ x.property.1).preimage_mem_nhds
        (ball_mem_nhds wx.val hs))
  obtain ⟨t, ht, hsub⟩ := Metric.mem_nhds_iff.mp hn
  have hdiff : ∀ v ∈ ball x.val t,
      HasFDerivAt (fun z => Y z - X z) (0 : ℂ →L[ℝ] (ℝ × ℝ × ℝ)) v := by
    intro v hv
    have hv' := hsub hv
    have hy : HasFDerivAt Y (infinityRealDifferential k v) v :=
      hasFDerivAt_realPrimitive_chartInversion hk hv'.1.1
        (hd₁ _ hv'.2) (hd₂ _ hv'.2) (hd₃ _ hv'.2)
    convert hy.sub (hX v (by simpa using hv'.1.2)) using 1 <;> first | rfl | simp
  have hc : ∀ v ∈ ball x.val t, Y v - X v = -X x.val := by
    intro v hv
    have he := isOpen_ball.is_const_of_fderiv_eq_zero (convex_ball x.val t).isPreconnected
      (fun z hz => (hdiff z hz).differentiableAt.differentiableWithinAt)
      (fun z hz => (hdiff z hz).fderiv) hv (mem_ball_self ht)
    simpa [hYx] using he
  have hev : ∀ᶠ v : infinityOverlap r in 𝓝 x, v.val ∈ ball x.val t :=
    continuous_subtype_val.continuousAt.preimage_mem_nhds (ball_mem_nhds x.val ht)
  filter_upwards [hev] with v hv
  have hrep := hrepr (infinityOverlapPoint hk hr v) (hsub hv).2
  change descendedIntegral hk b (infinityOverlapPoint hk hr v) =
    descendedIntegral hk b wx + projectPeriod (Y v.val) at hrep
  rw [hrep]
  have he := congrArg projectPeriod (hc v.val hv)
  rw [projectPeriod_sub] at he
  have hnX : projectPeriod (-X x.val) = -projectPeriod (X x.val) := by
    simp [projectPeriod]
  rw [hnX] at he
  change _ = descendedIntegral hk b wx - projectPeriod (X x.val)
  rw [add_sub_assoc, he, sub_eq_add_neg]

/-- A single quotient constant works on the entire punctured overlap. -/
theorem infinity_primitive_identification {k : ℕ} (hk : 2 ≤ k)
    (b : PuncturedPlane k) {r : ℝ} (hr0 : 0 < r) (hr : r ≤ 1)
    (X : ℂ → ℝ × ℝ × ℝ)
    (hX : ∀ v ∈ ball (0 : ℂ) r, HasFDerivAt X (infinityRealDifferential k v) v) :
    ∃ C : PeriodTarget, ∀ v : infinityOverlap r,
      descendedIntegral hk b (infinityOverlapPoint hk hr v) = C + projectPeriod (X v.val) := by
  let : PreconnectedSpace (infinityOverlap r) :=
    isPreconnected_iff_preconnectedSpace.mp (isPreconnected_infinityOverlap r)
  have hhalf : 0 < r / 2 := half_pos hr0
  have hx : (↑(r / 2) : ℂ) ∈ infinityOverlap r := by
    constructor
    · exact_mod_cast ne_of_gt hhalf
    · simpa [Complex.norm_real, abs_of_pos hr0] using half_lt_self hr0
  let x : infinityOverlap r := ⟨(r / 2 : ℝ), hx⟩
  refine ⟨descendedIntegral hk b (infinityOverlapPoint hk hr x) - projectPeriod (X x.val), ?_⟩
  intro v
  exact sub_eq_iff_eq_add.mp
    ((infinity_difference_locally_constant hk b hr X hX).apply_eq_of_preconnectedSpace v x)

/-- The actual descended integral has a smooth nondegenerate infinity representative,
identified on the whole overlap with one constant. -/
theorem exists_integrated_infinity_chart {k : ℕ} (hk : 2 ≤ k) (b : PuncturedPlane k) :
    ∃ r : ℝ, ∃ _hr0 : 0 < r, ∃ hr1 : r < 1,
    ∃ X : ℂ → ℝ × ℝ × ℝ, ∃ C : PeriodTarget,
      X 0 = 0 ∧ ContDiffOn ℝ ∞ X (ball (0 : ℂ) r) ∧
      (∀ v ∈ ball (0 : ℂ) r, HasFDerivAt X (infinityRealDifferential k v) v) ∧
      (∀ v ∈ ball (0 : ℂ) r, Function.Injective (infinityRealDifferential k v)) ∧
      (∀ v : infinityOverlap r,
        descendedIntegral hk b (infinityOverlapPoint hk hr1.le v) = C + projectPeriod (X v.val)) := by
  obtain ⟨r, hr0, hr1, X, hzero, hsmooth, hder, hinj⟩ := exists_smooth_infinity_primitive hk
  obtain ⟨C, hC⟩ := infinity_primitive_identification hk b hr0 hr1.le X hder
  exact ⟨r, hr0, hr1, X, C, hzero, hsmooth, hder, hinj, hC⟩

end KsIndex.KarcherData
