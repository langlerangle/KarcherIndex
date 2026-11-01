module

public import KsIndexLean.DirichletDisplacement
public import KsIndexLean.SeamMollificationSupport
public import KsIndexLean.FiniteMollificationHoles

@[expose] public section


/-!
# Smooth approximation near a natural Dirichlet boundary

For a trace-zero function localized in a seam domain, mollification followed by
dilation gives smooth approximants vanishing near the whole unit circle and on
its exterior. For each approximant the vanishing neighborhood has a positive
width, uniform over circle points; the width may depend on the approximation
index. The supports eventually lie in the seam domain, and the values and
product-rule derivatives converge in L² over the plane. The construction
commutes with multiplication by complex scalars.
-/

open Set MeasureTheory Filter Topology Metric
open scoped ContDiff
noncomputable section
namespace KsIndex.Trace
open KsIndex.WeakH1 KsIndex.Bracket

/-- The dilated function's support is contained in the inverse-dilated support. -/
lemma tsupport_comp_smul {g : ℂ → ℂ} {c : ℝ} (hc : c ≠ 0) :
    tsupport (fun z => g (c • z)) ⊆ (fun z => c⁻¹ • z) '' tsupport g := by
  have himg : (fun z : ℂ => c⁻¹ • z) '' tsupport g =
      (fun z : ℂ => c • z) ⁻¹' tsupport g := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      simp only [mem_preimage, smul_smul, mul_inv_cancel₀ hc, one_smul]
      exact hx
    · intro hy
      refine ⟨c • y, hy, ?_⟩
      change c⁻¹ • c • y = y
      rw [smul_smul, inv_mul_cancel₀ hc, one_smul]
  rw [himg]
  apply closure_minimal
  · intro z hz
    simp only [mem_preimage]
    exact subset_closure (Function.mem_support.mpr hz)
  · exact IsClosed.preimage (continuous_const_smul c) isClosed_closure

lemma shrinkingMollifier_rOut_le_one (n : ℕ) : (shrinkingMollifier n).rOut ≤ 1 := by
  simp only [shrinkingMollifier]
  rw [div_le_one (by positivity)]
  linarith [Nat.cast_nonneg (α := ℝ) n]

/-- **Eventual seam-domain support of the displaced mollifications**: the
mollified support thickens by rOut, the inverse dilation moves any
point of the (bounded) thickened support by at most `(1 − c⁻¹)·3`, and both
go to `0` — so the compact-in-open containment recovers eventually via the
`infEDist` triangle (no nonemptiness side conditions). -/
theorem dilated_mollify_support_seam {A : Set Circle₁} (hA : IsOpen A)
    {u : ℂ → ℂ} (hcu : HasCompactSupport u)
    (hsu : tsupport u ⊆ (seamDomain A hA : Set ℂ)) :
    ∀ᶠ n in atTop, tsupport (fun z =>
        compactMollify (shrinkingMollifier n) u (dilationFactor n • z)) ⊆
      (seamDomain A hA : Set ℂ) := by
  obtain ⟨ε, hε, hsub⟩ := hcu.exists_cthickening_subset_open
    (seamDomain A hA).isOpen hsu
  have hub : tsupport u ⊆ Metric.closedBall (0 : ℂ) 2 := by
    intro z hz
    have hcol := (hsu hz).1
    have h2 : ‖z‖ < 2 := hcol.2
    simpa [Metric.mem_closedBall, dist_zero_right] using h2.le
  have hcinv : Tendsto (fun n => 1 - (dilationFactor n)⁻¹) atTop (𝓝 0) := by
    have hinv : Tendsto (fun n => (dilationFactor n)⁻¹) atTop (𝓝 1) := by
      have := dilationFactor_tendsto.inv₀ one_ne_zero
      simpa using this
    have := (tendsto_const_nhds :
      Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1)).sub hinv
    simpa using this
  have hsmall : ∀ᶠ n in atTop,
      (1 - (dilationFactor n)⁻¹) * 3 + (shrinkingMollifier n).rOut < ε := by
    have hsum : Tendsto (fun n =>
        (1 - (dilationFactor n)⁻¹) * 3 + (shrinkingMollifier n).rOut)
        atTop (𝓝 0) := by
      simpa using (hcinv.mul_const 3).add shrinkingMollifier_radius
    exact hsum.eventually (gt_mem_nhds hε)
  filter_upwards [hsmall] with n hn
  have hcn1 : (1 : ℝ) ≤ dilationFactor n := one_le_dilationFactor n
  have hcn0 : dilationFactor n ≠ 0 := (lt_of_lt_of_le one_pos hcn1).ne'
  have hcinv1 : (dilationFactor n)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hcn1
  intro y hy
  obtain ⟨x, hx, rfl⟩ := tsupport_comp_smul hcn0 hy
  have hx2 := compactMollify_tsupport_subset (shrinkingMollifier n) u hx
  -- ‖x‖ ≤ 3
  have hx3 : ‖x‖ ≤ 3 := by
    have hb : cthickening (shrinkingMollifier n).rOut (tsupport u) ⊆
        cthickening (shrinkingMollifier n).rOut (Metric.closedBall (0 : ℂ) 2) :=
      cthickening_subset_of_subset _ hub
    have hx4 := hb hx2
    rw [cthickening_closedBall (shrinkingMollifier n).rOut_pos.le
      (by norm_num : (0 : ℝ) ≤ 2)] at hx4
    simp only [Metric.mem_closedBall, dist_zero_right] at hx4
    linarith [shrinkingMollifier_rOut_le_one n]
  -- dist (c⁻¹ • x) x ≤ (1 − c⁻¹)·3
  have hdist : dist ((dilationFactor n)⁻¹ • x) x ≤
      (1 - (dilationFactor n)⁻¹) * 3 := by
    rw [dist_eq_norm]
    have he : (dilationFactor n)⁻¹ • x - x =
        ((dilationFactor n)⁻¹ - 1) • x := by
      rw [sub_smul, one_smul]
    rw [he, norm_smul, Real.norm_eq_abs,
      abs_of_nonpos (by linarith : (dilationFactor n)⁻¹ - 1 ≤ 0)]
    nlinarith [norm_nonneg x]
  -- infEDist triangle into the ε-cthickening
  apply hsub
  rw [mem_cthickening_iff]
  calc infEDist ((dilationFactor n)⁻¹ • x) (tsupport u)
      ≤ edist ((dilationFactor n)⁻¹ • x) x + infEDist x (tsupport u) :=
        infEDist_le_edist_add_infEDist
    _ ≤ ENNReal.ofReal ((1 - (dilationFactor n)⁻¹) * 3) +
        ENNReal.ofReal (shrinkingMollifier n).rOut := by
        gcongr
        · rw [edist_dist]
          exact ENNReal.ofReal_le_ofReal hdist
        · exact mem_cthickening_iff.mp hx2
    _ = ENNReal.ofReal ((1 - (dilationFactor n)⁻¹) * 3 +
        (shrinkingMollifier n).rOut) := by
        rw [← ENNReal.ofReal_add (by nlinarith) (shrinkingMollifier n).rOut_pos.le]
    _ ≤ ENNReal.ofReal ε := ENNReal.ofReal_le_ofReal hn.le

/-- Complex-scalar equivariance of mollification followed by dilation: scalar
multiplication commutes with convolution and pointwise precomposition. -/
lemma dilated_mollify_phase (φ : ContDiffBump (0 : ℂ)) {u : ℂ → ℂ}
    (c : ℂ) (r : ℝ) :
    (fun z => compactMollify φ (fun w => c • u w) (r • z)) =
      fun z => c • compactMollify φ u (r • z) := by
  funext z
  change compactMollify φ (c • u) (r • z) = c • compactMollify φ u (r • z)
  simp only [compactMollify, convolution_def, ContinuousLinearMap.lsmul_apply,
    Pi.smul_apply]
  rw [← integral_smul]
  congr 1
  funext t
  exact smul_comm _ _ _

/-- A localized trace-zero function admits smooth approximants vanishing near
the whole unit circle and on its exterior. The positive neighborhood width may
depend on the approximation index. Supports eventually lie in the seam domain;
values and each directional derivative converge in L² over the plane to the
localized value and its full product-rule jet. -/
theorem dirichlet_layer_approximation {A : Set Circle₁} (hA : IsOpen A)
    (u : ComplexH1) (hm : arcTrace A u = 0) {χ : ℂ → ℝ}
    (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ)
    (hs : tsupport χ ⊆ (seamDomain A hA : Set ℂ)) :
    let v := fun z => χ z • joinedDiskValue u 0 0 z
    let W := fun z => χ z • joinedDiskJet u 0 0 z +
      (fderiv ℝ χ z).smulRight (joinedDiskValue u 0 0 z)
    ∃ (_hv : MemLp v 2 volume) (_hW : ∀ d, MemLp (fun z => W z d) 2 volume),
    ∃ f : ℕ → ℂ → ℂ,
    ∃ (_hf : ∀ n, MemLp (f n) 2 volume)
      (_hfD : ∀ n d, MemLp (fun z => fderiv ℝ (f n) z d) 2 volume),
      (∀ n, ContDiff ℝ ∞ (f n)) ∧
      (∀ n, ∃ δ : ℝ, 0 < δ ∧ ∀ w p : ℂ, ‖p‖ = 1 → ‖w - p‖ < δ → f n w = 0) ∧
      (∀ (n : ℕ) (w : ℂ), 1 ≤ ‖w‖ → f n w = 0) ∧
      (∀ᶠ n in atTop, tsupport (f n) ⊆ (seamDomain A hA : Set ℂ)) ∧
      Tendsto (fun n => eLpNorm (fun z => f n z - v z) 2 volume) atTop (𝓝 0) ∧
      ∀ d, Tendsto (fun n =>
          eLpNorm (fun z => fderiv ℝ (f n) z d - W z d) 2 volume) atTop (𝓝 0) := by
  dsimp only
  obtain ⟨hw, hv, hJ⟩ := zero_join_weak_localization hA u hm hχ hc hs
  have hcv : HasCompactSupport (fun z => χ z • joinedDiskValue u 0 0 z) :=
    hc.smul_right
  have hcJ : ∀ d, HasCompactSupport (fun z =>
      (χ z • joinedDiskJet u 0 0 z +
        (fderiv ℝ χ z).smulRight (joinedDiskValue u 0 0 z)) d) :=
    localized_jet_compact hc (joinedDiskValue u 0 0) (joinedDiskJet u 0 0)
  have hvan : ∀ z : ℂ, 1 < ‖z‖ → χ z • joinedDiskValue u 0 0 z = 0 :=
    fun z hz => localized_zero_join_vanish u χ hz
  have hsupp : tsupport (fun z => χ z • joinedDiskValue u 0 0 z) ⊆
      (seamDomain A hA : Set ℂ) :=
    (tsupport_smul_subset_left χ _).trans hs
  have hcn0 : ∀ n, dilationFactor n ≠ 0 := fun n =>
    (lt_of_lt_of_le one_pos (one_le_dilationFactor n)).ne'
  refine ⟨hv, hJ, fun n z =>
    compactMollify (shrinkingMollifier n)
      (fun w => χ w • joinedDiskValue u 0 0 w) (dilationFactor n • z),
    fun n => MemLp.comp_smul (compactMollify_memLp _ hv hcv) (hcn0 n), ?_,
    fun n => contDiff_dilated_mollify _ hv _, ?_, ?_, ?_, ?_, ?_⟩
  · -- MemLp of the classical jets, via the chain-rule identification
    intro n d
    have hid : (fun z => fderiv ℝ (fun w =>
        compactMollify (shrinkingMollifier n)
          (fun w' => χ w' • joinedDiskValue u 0 0 w') (dilationFactor n • w)) z d) =
        fun z => dilationFactor n • compactMollify (shrinkingMollifier n)
          (fun w => (χ w • joinedDiskJet u 0 0 w +
            (fderiv ℝ χ w).smulRight (joinedDiskValue u 0 0 w)) d)
          (dilationFactor n • z) := by
      funext z
      rw [fderiv_comp_dilation (compactMollify_smooth _ hv) (dilationFactor n) z]
      simp only [smul_apply]
      rw [compactMollify_fderiv _ hv hw d]
    rw [hid]
    exact (MemLp.comp_smul (compactMollify_memLp _ (hJ d) (hcJ d))
      (hcn0 n)).const_smul (dilationFactor n)
  · intro n
    refine ⟨(shrinkingMollifier n).rOut /
      (2 * (1 + (shrinkingMollifier n).rOut)), ?_, ?_⟩
    · have := (shrinkingMollifier n).rOut_pos
      positivity
    · intro w p hp hwp
      exact dilated_mollify_vanish_near_circle n hvan w p hp hwp
  · exact fun n w hw => dilated_mollify_vanish_exterior n hvan w hw
  · exact dilated_mollify_support_seam hA hcv hsupp
  · exact tendsto_dilated_mollify_value hv hcv
  · intro d
    exact tendsto_dilated_mollify_jet hv hJ hcJ hw d

end KsIndex.Trace

