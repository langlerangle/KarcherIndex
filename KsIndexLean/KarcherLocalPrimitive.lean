module

public import KsIndexLean.KarcherDescent
public import Mathlib.Analysis.Complex.HasPrimitives
public import Mathlib.Analysis.Complex.RealDeriv

@[expose] public section


/-! Local primitive representatives for the actual quotient-valued EW integral. -/
noncomputable section
open Set
open scoped Topology
namespace KsIndex.Piecewise

/-- The fundamental theorem on an actual straight piece, with its contour convention. -/
lemma linePiece_contour_eq_sub {a b : ℂ} {f F : ℂ → ℂ}
    (hf : ContinuousOn f (linePiece a b).image)
    (hF : ∀ z ∈ (linePiece a b).image, HasDerivAt F (f z) z) :
    (linePiece a b).contour f = F b - F a := by
  have hd : ∀ t ∈ Set.uIcc (0 : ℝ) 1,
      HasDerivAt (fun t : ℝ => F (a + (t : ℂ) * (b - a)))
        ((b - a) * f (a + (t : ℂ) * (b - a))) t := by
    intro t ht
    have ht' : t ∈ Icc (0 : ℝ) 1 := by simpa using ht
    have hz : a + (t : ℂ) * (b - a) ∈ (linePiece a b).image :=
      ⟨t, ht', rfl⟩
    have hl : HasDerivAt (fun t : ℝ => a + (t : ℂ) * (b - a)) (b - a) t := by
      simpa using (Complex.ofRealCLM.hasDerivAt.mul_const (b - a)).const_add a
    simpa [Function.comp_def, smul_eq_mul] using (hF _ hz).scomp t hl
  have hi := (linePiece a b).integrable_of_continuousOn hf
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt hd hi
  simpa [Piece.contour, linePiece] using he

end KsIndex.Piecewise

namespace KsIndex.Piecewise

lemma linePiece_image_subset_of_convex {U : Set ℂ} (hU : Convex ℝ U)
    {a b : ℂ} (ha : a ∈ U) (hb : b ∈ U) : (linePiece a b).image ⊆ U := by
  rintro z ⟨t, ht, rfl⟩
  simpa [linePiece, AffineMap.lineMap_apply, Complex.real_smul] using
    hU.add_smul_sub_mem ha hb ht

end KsIndex.Piecewise

namespace KsIndex.KarcherData
open Piecewise

/-- Local primitives recover increments of the previously constructed integral map. -/
theorem descendedIntegral_eq_local_primitives {k : ℕ} (hk : 2 ≤ k)
    (b x y : PuncturedPlane k) {U : Set ℂ} (hU : Convex ℝ U)
    (havoid : ∀ z ∈ U, z ∉ Surface.punctures k)
    (hx : x.val ∈ U) (hy : y.val ∈ U) (F₁ F₂ F₃ : ℂ → ℂ)
    (h₁ : ∀ z ∈ U, HasDerivAt F₁ (coeff1 k z) z)
    (h₂ : ∀ z ∈ U, HasDerivAt F₂ (coeff2 k z) z)
    (h₃ : ∀ z ∈ U, HasDerivAt F₃ (coeff3 k z) z) :
    descendedIntegral hk b y = descendedIntegral hk b x +
      projectPeriod ((F₁ y.val - F₁ x.val).re,
        (F₂ y.val - F₂ x.val).re, (F₃ y.val - F₃ x.val).re) := by
  let p := linePiece x.val y.val
  have himage : p.image ⊆ U := linePiece_image_subset_of_convex hU hx hy
  have hp : ∀ z ∈ Surface.punctures k, (Chain.singleton p).Avoids z := by
    intro z hz
    apply Chain.singleton_avoids
    intro t ht he
    exact havoid _ (himage ⟨t, ht, rfl⟩) (he ▸ hz)
  have hc₁ : ContinuousOn (coeff1 k) p.image := fun z hz =>
    (differentiableAt_coeff1 (havoid z (himage hz))).continuousAt.continuousWithinAt
  have hc₂ : ContinuousOn (coeff2 k) p.image := fun z hz =>
    (differentiableAt_coeff2 (havoid z (himage hz))).continuousAt.continuousWithinAt
  have hc₃ : ContinuousOn (coeff3 k) p.image := fun z hz =>
    (differentiableAt_coeff3 (havoid z (himage hz))).continuousAt.continuousWithinAt
  rw [descendedIntegral_increment hk b x y (Chain.singleton p)
    (by simp [p]) (by simp [p]) hp]
  simp only [quotientIntegral, periodVector, Chain.singleton_contour]
  rw [linePiece_contour_eq_sub hc₁ (fun z hz => h₁ z (himage hz)),
    linePiece_contour_eq_sub hc₂ (fun z hz => h₂ z (himage hz)),
    linePiece_contour_eq_sub hc₃ (fun z hz => h₃ z (himage hz))]

/-- Every finite non-puncture has normalized holomorphic primitives which represent
increments of the actual descended map. The derivatives are the prescribed EW data. -/
theorem exists_local_primitives {k : ℕ} (hk : 2 ≤ k)
    (b x : PuncturedPlane k) :
    ∃ r : ℝ, 0 < r ∧ ∃ F₁ F₂ F₃ : ℂ → ℂ,
      F₁ x.val = 0 ∧ F₂ x.val = 0 ∧ F₃ x.val = 0 ∧
      (∀ z ∈ Metric.ball x.val r, HasDerivAt F₁ (coeff1 k z) z) ∧
      (∀ z ∈ Metric.ball x.val r, HasDerivAt F₂ (coeff2 k z) z) ∧
      (∀ z ∈ Metric.ball x.val r, HasDerivAt F₃ (coeff3 k z) z) ∧
      ∀ y : PuncturedPlane k, y.val ∈ Metric.ball x.val r →
        descendedIntegral hk b y = descendedIntegral hk b x +
          projectPeriod ((F₁ y.val).re, (F₂ y.val).re, (F₃ y.val).re) := by
  have hclosed : IsClosed (Surface.punctures k) :=
    isClosed_eq (continuous_id.pow (2 * k)) continuous_const
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hclosed.isOpen_compl x.val x.property
  have havoid : ∀ z ∈ Metric.ball x.val r, z ∉ Surface.punctures k :=
    fun z hz => hball hz
  have hd₁ : DifferentiableOn ℂ (coeff1 k) (Metric.ball x.val r) :=
    fun z hz => (differentiableAt_coeff1 (havoid z hz)).differentiableWithinAt
  have hd₂ : DifferentiableOn ℂ (coeff2 k) (Metric.ball x.val r) :=
    fun z hz => (differentiableAt_coeff2 (havoid z hz)).differentiableWithinAt
  have hd₃ : DifferentiableOn ℂ (coeff3 k) (Metric.ball x.val r) :=
    fun z hz => (differentiableAt_coeff3 (havoid z hz)).differentiableWithinAt
  obtain ⟨F₁, hF₁, h₁⟩ := hd₁.isExactOn_ball.with_val_at x.val 0
  obtain ⟨F₂, hF₂, h₂⟩ := hd₂.isExactOn_ball.with_val_at x.val 0
  obtain ⟨F₃, hF₃, h₃⟩ := hd₃.isExactOn_ball.with_val_at x.val 0
  refine ⟨r, hr, F₁, F₂, F₃, hF₁, hF₂, hF₃, h₁, h₂, h₃, ?_⟩
  intro y hy
  simpa [hF₁, hF₂, hF₃] using descendedIntegral_eq_local_primitives hk b x y
    (convex_ball x.val r) havoid (Metric.mem_ball_self hr) hy F₁ F₂ F₃ h₁ h₂ h₃

/-- The finite parameter chart carries the subspace topology from ℂ. -/
instance {k : ℕ} : TopologicalSpace (PuncturedPlane k) :=
  inferInstanceAs (TopologicalSpace {w : ℂ // w ∉ Surface.punctures k})

lemma continuous_projectPeriod : Continuous projectPeriod := by
  exact continuous_fst.prodMk (continuous_fst.comp continuous_snd |>.prodMk
    (continuous_quotient_mk'.comp (continuous_snd.comp continuous_snd)))

/-- Continuity belongs to the actual descended map, independently of selected paths. -/
theorem continuous_descendedIntegral {k : ℕ} (hk : 2 ≤ k) (b : PuncturedPlane k) :
    Continuous (descendedIntegral hk b) := by
  apply continuous_iff_continuousAt.mpr
  intro x
  obtain ⟨r, hr, F₁, F₂, F₃, hF₁, hF₂, hF₃, h₁, h₂, h₃, hrepr⟩ :=
    exists_local_primitives hk b x
  have hx : x.val ∈ Metric.ball x.val r := Metric.mem_ball_self hr
  have hc₁ : ContinuousAt (fun y : PuncturedPlane k => F₁ y.val) x :=
    (h₁ x.val hx).continuousAt.comp
    (continuous_subtype_val.continuousAt (x := x))
  have hc₂ : ContinuousAt (fun y : PuncturedPlane k => F₂ y.val) x :=
    (h₂ x.val hx).continuousAt.comp
    (continuous_subtype_val.continuousAt (x := x))
  have hc₃ : ContinuousAt (fun y : PuncturedPlane k => F₃ y.val) x :=
    (h₃ x.val hx).continuousAt.comp
    (continuous_subtype_val.continuousAt (x := x))
  have hlocal : ContinuousAt (fun y : PuncturedPlane k =>
      descendedIntegral hk b x + projectPeriod
        ((F₁ y.val).re, (F₂ y.val).re, (F₃ y.val).re)) x :=
    continuousAt_const.add (continuous_projectPeriod.continuousAt.comp
      ((Complex.continuous_re.continuousAt.comp hc₁).prodMk
        ((Complex.continuous_re.continuousAt.comp hc₂).prodMk
          (Complex.continuous_re.continuousAt.comp hc₃))))
  apply hlocal.congr_of_eventuallyEq
  have hn : ∀ᶠ y : PuncturedPlane k in 𝓝 x, y.val ∈ Metric.ball x.val r :=
    continuous_subtype_val.continuousAt.preimage_mem_nhds (Metric.ball_mem_nhds x.val hr)
  filter_upwards [hn] with y hy
  exact hrepr y hy

end KsIndex.KarcherData
