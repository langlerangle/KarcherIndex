module

public import KsIndexLean.EndpointRepresentative
public import KsIndexLean.AnnularSpine
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

@[expose] public section


/-! # Weak polar pullback on an annulus

This module develops radial slices of planar functions on an open annulus
`a < ‖w‖ < b`, with `0 < a`, as circle-valued L² data. It supplies polar
change of variables, null-set transport, measurability and integrability of
the slice map, and identities for transporting weak derivative data.
Slices are defined directly on the circle subtype. Angular coordinates
enter the change-of-variables proof through the window starting at `−π`.

The weighted slice norm recovers the planar L² norm. Radial derivative
energy is bounded by full directional energy; no reverse estimate is
asserted. For example, `w/‖w‖` has zero radial derivative but nonzero angular
derivative. Endpoint evaluation and trace estimates are separate results. -/

open MeasureTheory Set TopologicalSpace intervalIntegral
open scoped Topology ENNReal NNReal Distributions

noncomputable section

namespace KsIndex.Trace

section Annulus

variable {a b : ℝ}

/-- The open annulus `a < ‖w‖ < b` as an `Opens ℂ`. -/
def annulusOpens (a b : ℝ) : Opens ℂ :=
  ⟨{w : ℂ | a < ‖w‖ ∧ ‖w‖ < b},
    (isOpen_lt continuous_const continuous_norm).inter
      (isOpen_lt continuous_norm continuous_const)⟩

lemma mem_annulusOpens {w : ℂ} : w ∈ annulusOpens a b ↔ a < ‖w‖ ∧ ‖w‖ < b :=
  Iff.rfl

lemma mem_annulusSet {w : ℂ} :
    w ∈ (annulusOpens a b : Set ℂ) ↔ a < ‖w‖ ∧ ‖w‖ < b := Iff.rfl

/-- The carrier set of the open annulus. -/
abbrev annulusSet (a b : ℝ) : Set ℂ := (annulusOpens a b : Set ℂ)

lemma measurableSet_annulusSet : MeasurableSet (annulusSet a b) :=
  (annulusOpens a b).isOpen.measurableSet

/-- Points of the annulus radius-scale into it from the circle. -/
lemma smul_circle_mem_annulusSet {t : ℝ} (ht : t ∈ Ioo a b) (ha : 0 < a)
    (w : Circle₁) : t • (w : ℂ) ∈ annulusSet a b := by
  have hw : ‖(w : ℂ)‖ = 1 := mem_sphere_zero_iff_norm.mp w.property
  have ht0 : 0 < t := lt_of_lt_of_le ha ht.1.le
  constructor <;>
    simp only [norm_smul, Real.norm_eq_abs, hw, mul_one, abs_of_pos ht0]
  · exact ht.1
  · exact ht.2

end Annulus

section Slice

variable {a b : ℝ}

/-- The radial slice of a planar function, directly on the circle subtype:
no angular interval appears. -/
def sliceFun (u : ℂ → ℂ) (t : ℝ) : Circle₁ → ℂ := fun w => u (t • (w : ℂ))

lemma sliceFun_apply (u : ℂ → ℂ) (t : ℝ) (w : Circle₁) :
    sliceFun u t w = u ((t : ℂ) * w) := by
  rw [sliceFun, Complex.real_smul]

end Slice

section MasterCoV

variable {a b : ℝ}

/-- The scaling map from the radius-circle product onto the plane. -/
def polarMul (p : ℝ × Circle₁) : ℂ := p.1 • (p.2 : ℂ)

lemma continuous_polarMul : Continuous polarMul :=
  (continuous_fst.smul (continuous_subtype_val.comp continuous_snd))

lemma measurable_polarMul : Measurable polarMul :=
  continuous_polarMul.measurable

/-- The circle lintegral through the window starting at `−π`. Changing between
open and half-open angular intervals only changes a null endpoint set. -/
lemma lintegral_circleMeasure_window_neg_pi {g : Circle₁ → ℝ≥0∞}
    (hg : Measurable g) :
    ∫⁻ w, g w ∂circleMeasure = ∫⁻ θ in Ioo (-Real.pi) Real.pi, g (circleParam θ) := by
  have hwin : Ico (-Real.pi) (-Real.pi + 2 * Real.pi) = Ico (-Real.pi) Real.pi := by
    congr 1
    ring
  rw [← map_circleParam_Ico (-Real.pi), hwin, lintegral_map hg measurable_circleParam,
    setLIntegral_congr (Ioo_ae_eq_Ico (a := -Real.pi) (b := Real.pi)).symm]

/-- **The master polar change of variables** (ENNReal level, measurable
integrand, no finiteness needed):
the annulus lintegral is the radially weighted iterated radius-circle
lintegral. -/
lemma lintegral_annulus_polar (ha : 0 < a) {f : ℂ → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ w in annulusSet a b, f w
      = ∫⁻ t in Ioo a b,
          ENNReal.ofReal t * ∫⁻ w, f (t • (w : ℂ)) ∂circleMeasure := by
  classical
  -- pass to the indicator and use the full-plane polar integration formula
  rw [← lintegral_indicator (measurableSet_annulusSet (a := a) (b := b)),
    ← Complex.lintegral_comp_polarCoord_symm]
  -- the target is the named product window (0,∞) × (−π, π)
  have htarget : (polarCoord.target : Set (ℝ × ℝ)) = Ioi 0 ×ˢ Ioo (-Real.pi) Real.pi :=
    rfl
  -- replace the chart formula by the explicit ray formula, globally
  have hsymm : ∀ p : ℝ × ℝ,
      ENNReal.ofReal p.1 •
          (annulusSet a b).indicator f (Complex.polarCoord.symm p)
        = ENNReal.ofReal p.1 •
            (annulusSet a b).indicator f ((p.1 : ℂ) * dir p.2) := by
    intro p
    rw [polarSymm_eq_dir]
  rw [setLIntegral_congr_fun (by rw [htarget]; exact measurableSet_Ioi.prod measurableSet_Ioo)
    (fun p _ => hsymm p)]
  -- product measure, then Tonelli
  have hmeas : Measurable fun p : ℝ × ℝ =>
      ENNReal.ofReal p.1 • (annulusSet a b).indicator f ((p.1 : ℂ) * dir p.2) := by
    simp only [smul_eq_mul]
    exact (ENNReal.measurable_ofReal.comp measurable_fst).mul
      ((hf.indicator measurableSet_annulusSet).comp (Continuous.measurable
        ((Complex.continuous_ofReal.comp continuous_fst).mul
          (Complex.continuous_exp.comp
            ((Complex.continuous_ofReal.comp continuous_snd).mul continuous_const)))))
  rw [htarget, Measure.volume_eq_prod ℝ ℝ, ← Measure.prod_restrict,
    MeasureTheory.lintegral_prod _ hmeas.aemeasurable]
  -- the inner integrand: membership is θ-free for t > 0
  have hinner : ∀ t ∈ Ioi (0 : ℝ),
      (∫⁻ θ in Ioo (-Real.pi) Real.pi,
          ENNReal.ofReal t • (annulusSet a b).indicator f ((t : ℂ) * dir θ))
        = (Ioo a b).indicator
            (fun t => ENNReal.ofReal t * ∫⁻ θ in Ioo (-Real.pi) Real.pi,
              f ((t : ℂ) * dir θ)) t := by
    intro t ht
    have hnorm : ∀ θ : ℝ, ‖(t : ℂ) * dir θ‖ = t := by
      intro θ
      rw [norm_mul, Complex.norm_real, norm_dir, mul_one, Real.norm_eq_abs,
        abs_of_pos ht]
    have hslicemeas : Measurable fun θ : ℝ => f ((t : ℂ) * dir θ) :=
      hf.comp (Continuous.measurable
        (continuous_const.mul (Complex.continuous_exp.comp
          (Complex.continuous_ofReal.mul continuous_const))))
    by_cases htI : t ∈ Ioo a b
    · rw [Set.indicator_of_mem htI]
      rw [← lintegral_const_mul _ hslicemeas]
      refine setLIntegral_congr_fun measurableSet_Ioo (fun θ _ => ?_)
      rw [Set.indicator_of_mem (mem_annulusSet.mpr (by rw [hnorm]; exact htI)),
        smul_eq_mul]
    · rw [Set.indicator_of_notMem htI]
      have hzero : ∀ θ ∈ Ioo (-Real.pi) Real.pi,
          ENNReal.ofReal t • (annulusSet a b).indicator f ((t : ℂ) * dir θ)
            = 0 := by
        intro θ _
        rw [Set.indicator_of_notMem
          (fun hmem => htI (by rw [← hnorm θ]; exact mem_annulusSet.mp hmem)),
          smul_zero]
      rw [setLIntegral_congr_fun measurableSet_Ioo hzero]
      simp
  have hcollapse : Ioo a b ∩ Ioi (0 : ℝ) = Ioo a b :=
    Set.inter_eq_left.mpr (fun t ht => lt_trans ha ht.1)
  rw [setLIntegral_congr_fun measurableSet_Ioi hinner,
    lintegral_indicator measurableSet_Ioo, Measure.restrict_restrict measurableSet_Ioo,
    hcollapse]
  -- identify the angular integral over the window starting at −π with circle measure
  refine setLIntegral_congr_fun measurableSet_Ioo (fun t _ => ?_)
  congr 1
  have hcirc : Measurable fun w : Circle₁ => f (t • (w : ℂ)) := by
    apply hf.comp
    apply Continuous.measurable
    exact (continuous_const : Continuous fun _ : Circle₁ => t).smul
      (continuous_subtype_val : Continuous fun w : Circle₁ => (w : ℂ))
  rw [lintegral_circleMeasure_window_neg_pi hcirc]
  refine setLIntegral_congr_fun measurableSet_Ioo (fun θ _ => ?_)
  rw [Complex.real_smul, circleParam_coe]

end MasterCoV

section NullTransport

variable {a b : ℝ}

/-- Radial-slice lintegrals of a measurable integrand are measurable in the radius
(the kernel-measurability Tonelli companion). -/
lemma measurable_slice_lintegral {f : ℂ → ℝ≥0∞} (hf : Measurable f) :
    Measurable fun t : ℝ => ∫⁻ w, f (t • (w : ℂ)) ∂circleMeasure := by
  have hunc : Measurable (Function.uncurry fun (t : ℝ) (w : Circle₁) =>
      f (t • (w : ℂ))) := hf.comp measurable_polarMul
  exact hunc.lintegral_prod_right

/-- Preimages of the circle slices are measurable. -/
lemma measurableSet_slicePreimage {N : Set ℂ} (hN : MeasurableSet N) (t : ℝ) :
    MeasurableSet {w : Circle₁ | t • (w : ℂ) ∈ N} := by
  have : Measurable fun w : Circle₁ => t • (w : ℂ) := by
    apply Continuous.measurable
    exact (continuous_const : Continuous fun _ : Circle₁ => t).smul
      (continuous_subtype_val : Continuous fun w : Circle₁ => (w : ℂ))
  exact this hN

/-- **Null-set transport, sliced form**: a set null in the annulus meets almost
every radial circle in a `σ`-null set.  The `a > 0` weight removal is where the
two-sided Jacobian comparison acts. -/
lemma slice_ae_null (ha : 0 < a) {N : Set ℂ} (hN : MeasurableSet N)
    (hN0 : volume (N ∩ annulusSet a b) = 0) :
    ∀ᵐ t ∂(volume.restrict (Ioo a b)),
      circleMeasure {w : Circle₁ | t • (w : ℂ) ∈ N} = 0 := by
  have hCoV := lintegral_annulus_polar (b := b) ha
    (f := N.indicator 1) (measurable_one.indicator hN)
  have hleft : (∫⁻ w in annulusSet a b, N.indicator 1 w) = 0 := by
    rw [lintegral_indicator_one hN, Measure.restrict_apply hN]
    exact hN0
  have hslice : ∀ t : ℝ, (∫⁻ w, N.indicator 1 (t • (w : ℂ)) ∂circleMeasure)
      = circleMeasure {w : Circle₁ | t • (w : ℂ) ∈ N} := by
    intro t
    rw [← lintegral_indicator_one (measurableSet_slicePreimage hN t)]
    refine lintegral_congr (fun w => ?_)
    by_cases hw : t • (w : ℂ) ∈ N
    · simp [Set.indicator]
    · simp [Set.indicator]
  rw [hleft] at hCoV
  have hmeas : Measurable fun t : ℝ =>
      ENNReal.ofReal t * ∫⁻ w, N.indicator 1 (t • (w : ℂ)) ∂circleMeasure :=
    ENNReal.measurable_ofReal.mul
      (measurable_slice_lintegral (measurable_one.indicator hN))
  have hae := (lintegral_eq_zero_iff hmeas).mp hCoV.symm
  rw [Filter.EventuallyEq, MeasureTheory.ae_restrict_iff' measurableSet_Ioo] at hae
  rw [MeasureTheory.ae_restrict_iff' measurableSet_Ioo]
  filter_upwards [hae] with t hprod htI
  have h0 := hprod htI
  rw [Pi.zero_apply, mul_eq_zero] at h0
  rcases h0 with h1 | h2
  · exact absurd h1 (by
      simp only [ENNReal.ofReal_eq_zero, not_le]
      exact lt_trans ha htI.1)
  · rw [← hslice t]
    exact h2

/-- **Null-set transport, product form**: the polar pullback of an annulus-null
set is product-null. -/
lemma prod_null_of_null (ha : 0 < a) {N : Set ℂ} (hN : MeasurableSet N)
    (hN0 : volume (N ∩ annulusSet a b) = 0) :
    ((volume.restrict (Ioo a b)).prod circleMeasure) (polarMul ⁻¹' N) = 0 := by
  rw [Measure.prod_apply (measurable_polarMul hN)]
  have h0 : ∀ᵐ t ∂(volume.restrict (Ioo a b)),
      circleMeasure (Prod.mk t ⁻¹' (polarMul ⁻¹' N)) = 0 := by
    filter_upwards [slice_ae_null ha hN hN0] with t ht
    exact ht
  rw [lintegral_congr_ae h0]
  simp

/-- **A.e.-strong-measurability transports through the polar pullback** — the
construction uses a strongly measurable representative, then transports
the null bad set (through a measurable superset). -/
lemma aestronglyMeasurable_pullback (ha : 0 < a) {u : ℂ → ℂ}
    (hu : AEStronglyMeasurable u (volume.restrict (annulusSet a b))) :
    AEStronglyMeasurable (fun p : ℝ × Circle₁ => u (polarMul p))
      ((volume.restrict (Ioo a b)).prod circleMeasure) := by
  obtain ⟨v, hv, huv⟩ := hu
  refine ⟨fun p => v (polarMul p), hv.comp_measurable measurable_polarMul, ?_⟩
  have hB : (volume.restrict (annulusSet a b)) {x | ¬u x = v x} = 0 :=
    MeasureTheory.ae_iff.mp huv
  obtain ⟨M, hBM, hM, hM0⟩ := exists_measurable_superset_of_null hB
  have hM0' : volume (M ∩ annulusSet a b) = 0 := by
    rwa [Measure.restrict_apply' measurableSet_annulusSet] at hM0
  have hMnull := prod_null_of_null ha hM hM0'
  rw [Filter.EventuallyEq, MeasureTheory.ae_iff]
  refine measure_mono_null (fun p hp => ?_) hMnull
  exact hBM hp

end NullTransport

section SliceLp

variable {a b : ℝ}

/-- The planar radial field of a weak Fréchet-derivative candidate: the honest
angular combination of the two APPLIED directional slices (never the operator
norm). -/
def radialField (U : ℂ → ℂ →L[ℝ] ℂ) : ℂ → ℂ :=
  fun z => (z.re / ‖z‖) • U z 1 + (z.im / ‖z‖) • U z Complex.I

/-- The radial derivative slice on the circle subtype. -/
def radSliceFun (U : ℂ → ℂ →L[ℝ] ℂ) (t : ℝ) : Circle₁ → ℂ :=
  fun w => (w : ℂ).re • U (t • (w : ℂ)) 1 + (w : ℂ).im • U (t • (w : ℂ)) Complex.I

/-- On positive radii the derivative slice IS the plain radial slice of the
planar field — one slicing machine serves both `F` and `G`. -/
lemma sliceFun_radialField {U : ℂ → ℂ →L[ℝ] ℂ} {t : ℝ} (ht : 0 < t) :
    sliceFun (radialField U) t = radSliceFun U t := by
  funext w
  have hw : ‖(w : ℂ)‖ = 1 := mem_sphere_zero_iff_norm.mp w.property
  have hnorm : ‖t • (w : ℂ)‖ = t := by
    rw [norm_smul, Real.norm_eq_abs, hw, mul_one, abs_of_pos ht]
  have hre : (t • (w : ℂ)).re = t * (w : ℂ).re := by
    rw [Complex.real_smul, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]
    ring
  have him : (t • (w : ℂ)).im = t * (w : ℂ).im := by
    rw [Complex.real_smul, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im]
    ring
  rw [sliceFun, radialField, radSliceFun, hnorm, hre, him]
  have ht' : t ≠ 0 := ne_of_gt ht
  congr 1
  · congr 1
    field_simp
  · congr 1
    field_simp

/-- The radial Bochner map: the `Lp`-class of the slice on good radii, with the
value zero outside the interval or where the slice is not in L². -/
def sliceLp (a b : ℝ) (u : ℂ → ℂ) (t : ℝ) : Lp ℂ 2 circleMeasure :=
  letI := Classical.propDecidable (t ∈ Ioo a b ∧ MemLp (sliceFun u t) 2 circleMeasure)
  if h : t ∈ Ioo a b ∧ MemLp (sliceFun u t) 2 circleMeasure
  then h.2.toLp (sliceFun u t) else 0

lemma sliceLp_of_memLp {u : ℂ → ℂ} {t : ℝ} (ht : t ∈ Ioo a b)
    (hm : MemLp (sliceFun u t) 2 circleMeasure) :
    sliceLp a b u t = hm.toLp (sliceFun u t) := by
  rw [sliceLp]
  split
  · rfl
  · next h => exact absurd ⟨ht, hm⟩ h

/-- The squared-norm change of variables, ENNReal level, for a MEASURABLE
representative (finiteness never assumed — the ENNReal-before-Bochner order). -/
lemma lintegral_annulus_sq (ha : 0 < a) {v : ℂ → ℂ} (hv : Measurable v) :
    ∫⁻ w in annulusSet a b, ‖v w‖ₑ ^ (2 : ℕ)
      = ∫⁻ t in Ioo a b,
          ENNReal.ofReal t * ∫⁻ w, ‖sliceFun v t w‖ₑ ^ (2 : ℕ) ∂circleMeasure :=
  lintegral_annulus_polar ha (hv.enorm.pow_const 2)

/-- A.e.-equality of the slice maps, from an annulus-null bad set. -/
lemma ae_slice_ae_eq (ha : 0 < a) {u v : ℂ → ℂ}
    (huv : u =ᵐ[volume.restrict (annulusSet a b)] v) :
    ∀ᵐ t ∂(volume.restrict (Ioo a b)),
      sliceFun u t =ᵐ[circleMeasure] sliceFun v t := by
  have hB : (volume.restrict (annulusSet a b)) {x | ¬u x = v x} = 0 :=
    MeasureTheory.ae_iff.mp huv
  obtain ⟨M, hBM, hM, hM0⟩ := exists_measurable_superset_of_null hB
  have hM0' : volume (M ∩ annulusSet a b) = 0 := by
    rwa [Measure.restrict_apply' measurableSet_annulusSet] at hM0
  filter_upwards [slice_ae_null ha hM hM0'] with t ht
  rw [Filter.EventuallyEq, MeasureTheory.ae_iff]
  refine measure_mono_null (fun w hw => ?_) ht
  exact hBM hw

/-- **A.e. slice membership**: an `L²` function on the annulus has `L²(σ)` slices
at almost every radius. -/
theorem ae_sliceFun_memLp (ha : 0 < a) {u : ℂ → ℂ}
    (hu : MemLp u 2 (volume.restrict (annulusSet a b))) :
    ∀ᵐ t ∂(volume.restrict (Ioo a b)), MemLp (sliceFun u t) 2 circleMeasure := by
  obtain ⟨v, hv, huv⟩ := hu.aestronglyMeasurable
  have hvmeas : Measurable v := hv.measurable
  have htr : ((2 : ℝ≥0∞)).toReal = ((2 : ℕ) : ℝ) := by norm_num
  have hfin_u : (∫⁻ w in annulusSet a b, ‖u w‖ₑ ^ (2 : ℕ)) < ∞ := by
    have h2 := (eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top
      (by norm_num : (2 : ℝ≥0∞) ≠ 0) (by norm_num : (2 : ℝ≥0∞) ≠ ∞) hu.aestronglyMeasurable).mp hu.eLpNorm_lt_top
    rw [htr] at h2
    simpa [ENNReal.rpow_natCast] using h2
  have hcong : (∫⁻ w in annulusSet a b, ‖v w‖ₑ ^ (2 : ℕ))
      = ∫⁻ w in annulusSet a b, ‖u w‖ₑ ^ (2 : ℕ) := by
    refine lintegral_congr_ae ?_
    filter_upwards [huv] with w hw
    rw [hw]
  have hfin_v : (∫⁻ w in annulusSet a b, ‖v w‖ₑ ^ (2 : ℕ)) < ∞ := by
    rw [hcong]
    exact hfin_u
  rw [lintegral_annulus_sq (b := b) ha hvmeas] at hfin_v
  have hinner_meas : Measurable fun t : ℝ =>
      ENNReal.ofReal t * ∫⁻ w, ‖sliceFun v t w‖ₑ ^ (2 : ℕ) ∂circleMeasure :=
    ENNReal.measurable_ofReal.mul
      (measurable_slice_lintegral (hvmeas.enorm.pow_const 2))
  have hae := ae_lt_top hinner_meas hfin_v.ne
  have hae2 : ∀ᵐ t ∂(volume.restrict (Ioo a b)),
      (∫⁻ w, ‖sliceFun v t w‖ₑ ^ (2 : ℕ) ∂circleMeasure) < ∞ := by
    rw [MeasureTheory.ae_restrict_iff' measurableSet_Ioo] at hae ⊢
    filter_upwards [hae] with t hlt htI
    have h1 := hlt htI
    by_contra hX
    rw [not_lt, top_le_iff] at hX
    have hne : ENNReal.ofReal t ≠ 0 := by
      simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]
      exact lt_trans ha htI.1
    rw [hX, ENNReal.mul_top hne] at h1
    exact absurd h1 (lt_irrefl ⊤)
  filter_upwards [hae2, ae_slice_ae_eq ha huv] with t hfin heq
  have hvSM : StronglyMeasurable (sliceFun v t) := by
    apply hv.comp_measurable
    apply Continuous.measurable
    exact (continuous_const : Continuous fun _ : Circle₁ => t).smul
      (continuous_subtype_val : Continuous fun w : Circle₁ => (w : ℂ))
  have hvMem : MemLp (sliceFun v t) 2 circleMeasure := by
    rw [memLp_iff]
    rw [eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top
      (by norm_num : (2 : ℝ≥0∞) ≠ 0) (by norm_num : (2 : ℝ≥0∞) ≠ ∞) hvSM.aestronglyMeasurable, htr]
    simpa [ENNReal.rpow_natCast] using hfin
  exact hvMem.ae_eq heq.symm

end SliceLp

section SliceMeasurability

variable {a b : ℝ}

lemma continuous_sliceFun_of_continuous {g : ℂ → ℂ} (hg : Continuous g) (t : ℝ) :
    Continuous (sliceFun g t) := by
  apply hg.comp
  exact (continuous_const : Continuous fun _ : Circle₁ => t).smul
    (continuous_subtype_val : Continuous fun w : Circle₁ => (w : ℂ))

/-- A continuous compactly supported function has `L²(σ)` slices at every
radius (σ is finite, the slice is bounded). -/
lemma memLp_sliceFun_of_continuous {g : ℂ → ℂ} (hg : Continuous g)
    (hgc : HasCompactSupport g) (t : ℝ) :
    MemLp (sliceFun g t) 2 circleMeasure := by
  obtain ⟨C, hC⟩ := hgc.exists_bound_of_continuous hg
  exact MemLp.of_bound
    (continuous_sliceFun_of_continuous hg t).aestronglyMeasurable C
    (Filter.Eventually.of_forall (fun w => hC _))

/-- The slice map of a continuous compactly supported function is CONTINUOUS
into `L²(σ)` on the open radius interval: the radial shift is uniform across
the fiber (`dist (t•w) (t₀•w) = |t − t₀|`), so uniform continuity of `g`
controls the sup distance of slices, and finiteness of `σ` converts it to the
`L²` distance. -/
lemma continuousOn_sliceLp_of_continuous {g : ℂ → ℂ} (hg : Continuous g)
    (hgc : HasCompactSupport g) :
    ContinuousOn (sliceLp a b g) (Ioo a b) := by
  intro t₀ ht₀
  rw [Metric.continuousWithinAt_iff]
  intro ε hε
  -- the σ-mass factor
  set Mσ : ℝ := ((circleMeasure Set.univ) ^ ((2 : ℝ≥0∞)).toReal⁻¹).toReal + 1 with hMσ
  have hMσpos : 0 < Mσ := by
    have : (0 : ℝ) ≤ ((circleMeasure Set.univ) ^ ((2 : ℝ≥0∞)).toReal⁻¹).toReal :=
      ENNReal.toReal_nonneg
    linarith
  -- uniform continuity of g
  have hgu : UniformContinuous g := hgc.uniformContinuous_of_continuous hg
  rw [Metric.uniformContinuous_iff] at hgu
  obtain ⟨δ', hδ', hδ'C⟩ := hgu (ε / (2 * Mσ)) (by positivity)
  refine ⟨δ', hδ', fun {t} ht hdist => ?_⟩
  -- both slices are honest Lp classes
  have hm := memLp_sliceFun_of_continuous hg hgc t
  have hm₀ := memLp_sliceFun_of_continuous hg hgc t₀
  rw [sliceLp_of_memLp ht hm, sliceLp_of_memLp ht₀ hm₀]
  -- the Lp distance is the eLpNorm of the difference
  have hdiff : (hm.toLp (sliceFun g t)) - (hm₀.toLp (sliceFun g t₀))
      = (hm.sub hm₀).toLp (sliceFun g t - sliceFun g t₀) :=
    (MemLp.toLp_sub hm hm₀).symm
  rw [dist_eq_norm, hdiff, Lp.norm_toLp]
  -- pointwise bound on the difference: the radial shift is fiber-uniform
  have hbound : ∀ w : Circle₁,
      ‖(sliceFun g t - sliceFun g t₀) w‖ ≤ ε / (2 * Mσ) := by
    intro w
    have hw : ‖(w : ℂ)‖ = 1 := mem_sphere_zero_iff_norm.mp w.property
    have hdw : dist (t • (w : ℂ)) (t₀ • (w : ℂ)) < δ' := by
      rw [dist_eq_norm, ← sub_smul, norm_smul, Real.norm_eq_abs, hw, mul_one]
      rw [Real.dist_eq] at hdist
      exact hdist
    exact le_of_lt (by
      have := hδ'C hdw
      rw [dist_eq_norm] at this
      exact this)
  have hsn : eLpNorm (sliceFun g t - sliceFun g t₀) 2 circleMeasure
      ≤ (circleMeasure Set.univ) ^ ((2 : ℝ≥0∞)).toReal⁻¹
          * ENNReal.ofReal (ε / (2 * Mσ)) :=
    eLpNorm_le_of_ae_bound
      ((continuous_sliceFun_of_continuous hg t).sub
        (continuous_sliceFun_of_continuous hg t₀)).aestronglyMeasurable
      (Filter.Eventually.of_forall hbound)
  have hfin : (circleMeasure Set.univ) ^ ((2 : ℝ≥0∞)).toReal⁻¹ ≠ ∞ := by
    apply ENNReal.rpow_ne_top_of_nonneg (by positivity)
    exact (measure_lt_top circleMeasure _).ne
  calc (eLpNorm (sliceFun g t - sliceFun g t₀) 2 circleMeasure).toReal
      ≤ (((circleMeasure Set.univ) ^ ((2 : ℝ≥0∞)).toReal⁻¹)
          * ENNReal.ofReal (ε / (2 * Mσ))).toReal := by
        apply ENNReal.toReal_mono
        · exact ENNReal.mul_ne_top hfin ENNReal.ofReal_ne_top
        · exact hsn
    _ = ((circleMeasure Set.univ) ^ ((2 : ℝ≥0∞)).toReal⁻¹).toReal
          * (ε / (2 * Mσ)) := by
        rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity)]
    _ ≤ Mσ * (ε / (2 * Mσ)) := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        rw [hMσ]
        linarith
    _ < ε := by
        rw [mul_div_assoc']
        rw [div_lt_iff₀ (by positivity : (0:ℝ) < 2 * Mσ)]
        ring_nf
        nlinarith [hMσpos, hε]

/-- The squared `L²` seminorm as a plain lintegral (the `rpow`/`pow` bridge,
done once). -/
lemma lintegral_enorm_sq_eq {α : Type*} [MeasurableSpace α] {μ : Measure α}
    (f : α → ℂ) (hf : AEStronglyMeasurable f μ) :
    ∫⁻ x, ‖f x‖ₑ ^ (2 : ℕ) ∂μ = (eLpNorm f 2 μ) ^ (2 : ℕ) := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num : (2 : ℝ≥0∞) ≠ 0)
    (by norm_num : (2 : ℝ≥0∞) ≠ ∞) hf]
  have htr : ((2 : ℝ≥0∞)).toReal = (2 : ℝ) := by norm_num
  rw [htr, ← ENNReal.rpow_natCast _ 2, ← ENNReal.rpow_mul]
  norm_num

/-- Slicing only sees the annulus: the indicator extension has the same slice
map. -/
lemma sliceLp_indicator_eq (ha : 0 < a) (u : ℂ → ℂ) :
    sliceLp a b ((annulusSet a b).indicator u) = sliceLp a b u := by
  funext t
  have hfun : ∀ _ : t ∈ Ioo a b,
      sliceFun ((annulusSet a b).indicator u) t = sliceFun u t := fun ht => by
    funext w
    rw [sliceFun, sliceFun,
      Set.indicator_of_mem (smul_circle_mem_annulusSet ht ha w)]
  rw [sliceLp, sliceLp]
  split
  · next h₁ =>
    split
    · next h₂ =>
      exact MemLp.toLp_congr h₁.2 h₂.2 ((hfun h₁.1) ▸ Filter.EventuallyEq.rfl)
    · next h₂ =>
      exact absurd ⟨h₁.1, (hfun h₁.1) ▸ h₁.2⟩ h₂
  · next h₁ =>
    split
    · next h₂ =>
      exact absurd ⟨h₂.1, (hfun h₂.1).symm ▸ h₂.2⟩ h₁
    · next _ => rfl

/-- **The measurability heart, measurable case**: the radial Bochner map of a
measurable `L²` function on the annulus is a.e.-strongly measurable on the
radius interval — by `L²` approximation with continuous compactly supported
functions, a summable-error subsequence-free convergence, and the continuity
of slices of continuous functions. -/
theorem aestronglyMeasurable_sliceLp_of_measurable (ha : 0 < a) {u : ℂ → ℂ}
    (hum : Measurable u) (hu : MemLp u 2 (volume.restrict (annulusSet a b))) :
    AEStronglyMeasurable (sliceLp a b u) (volume.restrict (Ioo a b)) := by
  classical
  -- reduce to the zero-extension, globally measurable and globally L²
  set u' : ℂ → ℂ := (annulusSet a b).indicator u with hu'def
  have hu'm : Measurable u' := hum.indicator measurableSet_annulusSet
  have hu'ae : u' =ᵐ[volume.restrict (annulusSet a b)] u :=
    indicator_ae_eq_restrict measurableSet_annulusSet
  have hu'r : MemLp u' 2 (volume.restrict (annulusSet a b)) := hu.ae_eq hu'ae.symm
  have hu'g : MemLp u' 2 volume := by
    rw [memLp_iff]
    rw [eLpNorm_indicator_eq_eLpNorm_restrict measurableSet_annulusSet]
    exact hu.eLpNorm_lt_top
  rw [← sliceLp_indicator_eq (b := b) ha u]
  -- the continuous approximants with summable error
  have hgex : ∀ n : ℕ, ∃ g : ℂ → ℂ, HasCompactSupport g ∧
      eLpNorm (u' - g) 2 volume ≤ (2 : ℝ≥0∞)⁻¹ ^ n ∧ Continuous g ∧
      MemLp g 2 volume :=
    fun n => hu'g.exists_hasCompactSupport_eLpNorm_sub_le (by norm_num)
      (pow_ne_zero n (ENNReal.inv_ne_zero.mpr (by norm_num)))
  choose g hgc hgnorm hgcont hgmem using hgex
  -- the per-approximant slice error, measured on circles
  set inner : ℕ → ℝ → ℝ≥0∞ := fun n t =>
    ∫⁻ w, ‖sliceFun (u' - g n) t w‖ₑ ^ (2 : ℕ) ∂circleMeasure with hinnerdef
  have hinnermeas : ∀ n, Measurable (inner n) := fun n =>
    measurable_slice_lintegral (((hu'm.sub (hgcont n).measurable)).enorm.pow_const 2)
  -- the weighted CoV bound: a · ∫ inner ≤ the L² error²
  have hbound : ∀ n, (∫⁻ t in Ioo a b, inner n t)
      ≤ (ENNReal.ofReal a)⁻¹ * ((2 : ℝ≥0∞)⁻¹ ^ n) ^ (2 : ℕ) := by
    intro n
    have hCoV := lintegral_annulus_sq (b := b) ha (hu'm.sub (hgcont n).measurable)
    have hwt : ENNReal.ofReal a * (∫⁻ t in Ioo a b, inner n t)
        ≤ ∫⁻ t in Ioo a b, ENNReal.ofReal t * inner n t := by
      rw [← lintegral_const_mul _ (hinnermeas n)]
      refine setLIntegral_mono_ae ((ENNReal.measurable_ofReal.comp measurable_id).mul
        (hinnermeas n)).aemeasurable ?_
      filter_upwards with t htI
      exact mul_le_mul' (ENNReal.ofReal_le_ofReal htI.1.le) le_rfl
    have hann : (∫⁻ w in annulusSet a b, ‖(u' - g n) w‖ₑ ^ (2 : ℕ))
        ≤ ((2 : ℝ≥0∞)⁻¹ ^ n) ^ (2 : ℕ) := by
      calc (∫⁻ w in annulusSet a b, ‖(u' - g n) w‖ₑ ^ (2 : ℕ))
          ≤ ∫⁻ w, ‖(u' - g n) w‖ₑ ^ (2 : ℕ) := setLIntegral_le_lintegral _ _
        _ = (eLpNorm (u' - g n) 2 volume) ^ (2 : ℕ) :=
          lintegral_enorm_sq_eq _ (hu'm.sub (hgcont n).measurable).aestronglyMeasurable
        _ ≤ ((2 : ℝ≥0∞)⁻¹ ^ n) ^ (2 : ℕ) := pow_le_pow_left' (hgnorm n) 2
    have h1 : ENNReal.ofReal a * (∫⁻ t in Ioo a b, inner n t)
        ≤ ((2 : ℝ≥0∞)⁻¹ ^ n) ^ (2 : ℕ) := by
      refine le_trans hwt ?_
      rw [← hCoV]
      exact hann
    have hane : ENNReal.ofReal a ≠ 0 := by
      simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]
      exact ha
    calc (∫⁻ t in Ioo a b, inner n t)
        = (ENNReal.ofReal a)⁻¹ * (ENNReal.ofReal a * ∫⁻ t in Ioo a b, inner n t) := by
          rw [← mul_assoc, ENNReal.inv_mul_cancel hane ENNReal.ofReal_ne_top, one_mul]
      _ ≤ (ENNReal.ofReal a)⁻¹ * ((2 : ℝ≥0∞)⁻¹ ^ n) ^ (2 : ℕ) :=
          mul_le_mul' le_rfl h1
  -- the summed error is finite, so the slice errors vanish a.e.
  have htsum : (∫⁻ t in Ioo a b, ∑' n, inner n t) < ∞ := by
    rw [lintegral_tsum (fun n => (hinnermeas n).aemeasurable)]
    calc (∑' n, ∫⁻ t in Ioo a b, inner n t)
        ≤ ∑' n, (ENNReal.ofReal a)⁻¹ * ((2 : ℝ≥0∞)⁻¹ ^ n) ^ (2 : ℕ) :=
          ENNReal.tsum_le_tsum hbound
      _ = (ENNReal.ofReal a)⁻¹ * ∑' n, ((4 : ℝ≥0∞)⁻¹) ^ n := by
          rw [ENNReal.tsum_mul_left]
          congr 1
          refine tsum_congr (fun n => ?_)
          rw [← pow_mul, mul_comm, pow_mul, ← ENNReal.inv_pow]
          norm_num
      _ < ∞ := by
          rw [ENNReal.tsum_geometric]
          apply ENNReal.mul_lt_top
          · simp only [ENNReal.inv_lt_top, ENNReal.ofReal_pos]
            exact ha
          · apply ENNReal.inv_lt_top.mpr
            simp only [tsub_pos_iff_lt]
            exact ENNReal.inv_lt_one.mpr (by norm_num)
  have haefin : ∀ᵐ t ∂(volume.restrict (Ioo a b)), (∑' n, inner n t) < ∞ :=
    ae_lt_top (Measurable.tsum hinnermeas) htsum.ne
  -- the limit identification, a.e. in the radius
  have haemem := ae_sliceFun_memLp ha hu'r
  have haelim : ∀ᵐ t ∂(volume.restrict (Ioo a b)),
      Filter.Tendsto (fun n => sliceLp a b (g n) t) Filter.atTop
        (𝓝 (sliceLp a b u' t)) := by
    filter_upwards [haefin, haemem, ae_restrict_mem measurableSet_Ioo]
      with t hsum hmem htI
    have hterms : Filter.Tendsto (fun n => inner n t) Filter.atTop (𝓝 0) :=
      ENNReal.tendsto_atTop_zero_of_tsum_ne_top hsum.ne
    rw [tendsto_iff_dist_tendsto_zero]
    have hdist : ∀ n, dist (sliceLp a b (g n) t) (sliceLp a b u' t)
        = ((inner n t) ^ ((2 : ℝ)⁻¹)).toReal := by
      intro n
      have hgm := memLp_sliceFun_of_continuous (hgcont n) (hgc n) t
      rw [sliceLp_of_memLp htI hgm, sliceLp_of_memLp htI hmem, dist_eq_norm,
        (MemLp.toLp_sub hgm hmem).symm, Lp.norm_toLp]
      have hfun : sliceFun (g n) t - sliceFun u' t
          = -(sliceFun (u' - g n) t) := by
        funext w
        simp [sliceFun]
      have hsn : eLpNorm (sliceFun (g n) t - sliceFun u' t) 2 circleMeasure
          = eLpNorm (sliceFun (u' - g n) t) 2 circleMeasure := by
        rw [hfun, eLpNorm_neg]
      rw [hsn]
      congr 1
      have h2 : inner n t
          = (eLpNorm (sliceFun (u' - g n) t) 2 circleMeasure) ^ (2 : ℕ) := by
        rw [hinnerdef]
        apply lintegral_enorm_sq_eq
        exact (hmem.sub hgm).aestronglyMeasurable
      rw [h2, ← ENNReal.rpow_natCast (eLpNorm _ 2 circleMeasure) 2,
        ← ENNReal.rpow_mul]
      norm_num
    refine Filter.Tendsto.congr (fun n => (hdist n).symm) ?_
    have hpow : Filter.Tendsto (fun n => (inner n t) ^ ((2 : ℝ)⁻¹))
        Filter.atTop (𝓝 0) := by
      have h0 : (0 : ℝ≥0∞) = (0 : ℝ≥0∞) ^ ((2 : ℝ)⁻¹) := by
        rw [ENNReal.zero_rpow_of_pos (by norm_num)]
      rw [h0]
      exact (ENNReal.continuous_rpow_const.tendsto 0).comp hterms
    have htoReal := (ENNReal.tendsto_toReal
      (by norm_num : (0 : ℝ≥0∞) ≠ ∞)).comp hpow
    simpa [Function.comp_def] using htoReal
  exact aestronglyMeasurable_of_tendsto_ae Filter.atTop
    (fun n => (continuousOn_sliceLp_of_continuous (hgcont n)
      (hgc n)).aestronglyMeasurable measurableSet_Ioo) haelim

/-- The radial `L²`-valued slice map of an `L²` function on an annulus with
positive inner radius is a.e.-strongly measurable on the radius interval.
The proof passes to a measurable representative and transfers back by a.e. equality. -/
theorem aestronglyMeasurable_sliceLp (ha : 0 < a) {u : ℂ → ℂ}
    (hu : MemLp u 2 (volume.restrict (annulusSet a b))) :
    AEStronglyMeasurable (sliceLp a b u) (volume.restrict (Ioo a b)) := by
  obtain ⟨v, hv, huv⟩ := hu.aestronglyMeasurable
  have hvr : MemLp v 2 (volume.restrict (annulusSet a b)) := hu.ae_eq huv
  refine (aestronglyMeasurable_sliceLp_of_measurable ha hv.measurable hvr).congr ?_
  filter_upwards [ae_slice_ae_eq ha huv, ae_sliceFun_memLp ha hu,
    ae_sliceFun_memLp ha hvr, ae_restrict_mem measurableSet_Ioo]
    with t heq hmu hmv htI
  rw [sliceLp_of_memLp htI hmv, sliceLp_of_memLp htI hmu]
  exact MemLp.toLp_congr hmv hmu heq.symm

/-- The square root is dominated by `1 + x` on `ℝ≥0∞` (the elementary
`L² ⊆ L¹`-on-finite-measure device). -/
lemma rpow_half_le_one_add (x : ℝ≥0∞) : x ^ ((2 : ℝ)⁻¹) ≤ 1 + x := by
  rcases le_or_gt x 1 with hx | hx
  · calc x ^ ((2 : ℝ)⁻¹) ≤ (1 : ℝ≥0∞) ^ ((2 : ℝ)⁻¹) :=
        ENNReal.rpow_le_rpow hx (by norm_num)
      _ = 1 := ENNReal.one_rpow _
      _ ≤ 1 + x := le_self_add
  · calc x ^ ((2 : ℝ)⁻¹) ≤ x ^ (1 : ℝ) :=
        ENNReal.rpow_le_rpow_of_exponent_le hx.le (by norm_num)
      _ = x := ENNReal.rpow_one x
      _ ≤ 1 + x := le_add_self

/-- The unweighted slice-square integral is finite: the `a > 0` weight removal
of the exact Jacobian identity. -/
lemma lintegral_slice_sq_lt_top (ha : 0 < a) {u : ℂ → ℂ}
    (hu : MemLp u 2 (volume.restrict (annulusSet a b))) :
    (∫⁻ t in Ioo a b,
      ∫⁻ w, ‖sliceFun u t w‖ₑ ^ (2 : ℕ) ∂circleMeasure) < ∞ := by
  obtain ⟨v, hv, huv⟩ := hu.aestronglyMeasurable
  have hvr : MemLp v 2 (volume.restrict (annulusSet a b)) := hu.ae_eq huv
  have hvm : Measurable v := hv.measurable
  have hcongr : (∫⁻ t in Ioo a b,
      ∫⁻ w, ‖sliceFun u t w‖ₑ ^ (2 : ℕ) ∂circleMeasure)
      = ∫⁻ t in Ioo a b,
          ∫⁻ w, ‖sliceFun v t w‖ₑ ^ (2 : ℕ) ∂circleMeasure := by
    refine lintegral_congr_ae ?_
    filter_upwards [ae_slice_ae_eq ha huv] with t heq
    refine lintegral_congr_ae ?_
    filter_upwards [heq] with w hw
    rw [hw]
  rw [hcongr]
  have hinnermeas : Measurable fun t : ℝ =>
      ∫⁻ w, ‖sliceFun v t w‖ₑ ^ (2 : ℕ) ∂circleMeasure :=
    measurable_slice_lintegral (hvm.enorm.pow_const 2)
  have hfin_v : (∫⁻ w in annulusSet a b, ‖v w‖ₑ ^ (2 : ℕ)) < ∞ := by
    have h2 := (eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top
      (by norm_num : (2 : ℝ≥0∞) ≠ 0) (by norm_num : (2 : ℝ≥0∞) ≠ ∞) hvr.aestronglyMeasurable).mp hvr.eLpNorm_lt_top
    have htr : ((2 : ℝ≥0∞)).toReal = ((2 : ℕ) : ℝ) := by norm_num
    rw [htr] at h2
    simpa [ENNReal.rpow_natCast] using h2
  have hane : ENNReal.ofReal a ≠ 0 := by
    simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]
    exact ha
  have hwt : ENNReal.ofReal a * (∫⁻ t in Ioo a b,
      ∫⁻ w, ‖sliceFun v t w‖ₑ ^ (2 : ℕ) ∂circleMeasure)
      ≤ ∫⁻ w in annulusSet a b, ‖v w‖ₑ ^ (2 : ℕ) := by
    rw [lintegral_annulus_sq (b := b) ha hvm, ← lintegral_const_mul _ hinnermeas]
    refine setLIntegral_mono_ae ((ENNReal.measurable_ofReal.comp measurable_id).mul
      hinnermeas).aemeasurable ?_
    filter_upwards with t htI
    exact mul_le_mul' (ENNReal.ofReal_le_ofReal htI.1.le) le_rfl
  calc (∫⁻ t in Ioo a b, ∫⁻ w, ‖sliceFun v t w‖ₑ ^ (2 : ℕ) ∂circleMeasure)
      = (ENNReal.ofReal a)⁻¹ * (ENNReal.ofReal a * ∫⁻ t in Ioo a b,
          ∫⁻ w, ‖sliceFun v t w‖ₑ ^ (2 : ℕ) ∂circleMeasure) := by
        rw [← mul_assoc, ENNReal.inv_mul_cancel hane ENNReal.ofReal_ne_top, one_mul]
    _ ≤ (ENNReal.ofReal a)⁻¹ * ∫⁻ w in annulusSet a b, ‖v w‖ₑ ^ (2 : ℕ) :=
        mul_le_mul' le_rfl hwt
    _ < ∞ := ENNReal.mul_lt_top
        (ENNReal.inv_lt_top.mpr (by simpa [ENNReal.ofReal_pos] using ha)) hfin_v

/-- The radial `L²`-valued slice map is integrable over the full finite radius
interval when `0 < a < b`. Endpoint values do not affect this integral; the
statement does not assert endpoint traces or continuity of the slice map. -/
theorem intervalIntegrable_sliceLp (ha : 0 < a) (hab : a < b) {u : ℂ → ℂ}
    (hu : MemLp u 2 (volume.restrict (annulusSet a b))) :
    IntervalIntegrable (sliceLp a b u) volume a b := by
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hab.le, IntegrableOn,
    ← Measure.restrict_congr_set (Ioo_ae_eq_Ioc (a := a) (b := b))]
  refine ⟨aestronglyMeasurable_sliceLp ha hu, ?_⟩
  rw [hasFiniteIntegral_iff_enorm]
  have henorm : ∀ᵐ t ∂(volume.restrict (Ioo a b)),
      ‖sliceLp a b u t‖ₑ = (∫⁻ w, ‖sliceFun u t w‖ₑ ^ (2 : ℕ) ∂circleMeasure)
        ^ ((2 : ℝ)⁻¹) := by
    filter_upwards [ae_sliceFun_memLp ha hu, ae_restrict_mem measurableSet_Ioo]
      with t hm htI
    rw [sliceLp_of_memLp htI hm, Lp.enorm_toLp,
      eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num : (2 : ℝ≥0∞) ≠ 0)
        (by norm_num : (2 : ℝ≥0∞) ≠ ∞) hm.aestronglyMeasurable]
    have htr : ((2 : ℝ≥0∞)).toReal = ((2 : ℕ) : ℝ) := by norm_num
    rw [htr]
    congr 1
    · refine lintegral_congr (fun w => ?_)
      rw [← ENNReal.rpow_natCast]
    · norm_num
  rw [lintegral_congr_ae henorm]
  calc (∫⁻ t in Ioo a b, (∫⁻ w, ‖sliceFun u t w‖ₑ ^ (2 : ℕ) ∂circleMeasure)
        ^ ((2 : ℝ)⁻¹))
      ≤ ∫⁻ t in Ioo a b,
          (1 + ∫⁻ w, ‖sliceFun u t w‖ₑ ^ (2 : ℕ) ∂circleMeasure) :=
        lintegral_mono (fun t => rpow_half_le_one_add _)
    _ = volume (Ioo a b) + ∫⁻ t in Ioo a b,
          ∫⁻ w, ‖sliceFun u t w‖ₑ ^ (2 : ℕ) ∂circleMeasure := by
        rw [lintegral_add_left measurable_const, setLIntegral_const, one_mul]
    _ < ∞ := ENNReal.add_lt_top.mpr
        ⟨by rw [Real.volume_Ioo]; exact ENNReal.ofReal_lt_top,
          lintegral_slice_sq_lt_top ha hu⟩

/-- The planar radial field of `L²` directional data is itself `L²` on the
annulus: `‖H‖ ≤ ‖U·1‖ + ‖U·I‖` pointwise there (the one-sided bound; NO
reverse bound exists — `w/‖w‖` is the counterexample). -/
lemma memLp_radialField (ha : 0 < a) {U : ℂ → ℂ →L[ℝ] ℂ}
    (hU1 : MemLp (fun w => U w 1) 2 (volume.restrict (annulusSet a b)))
    (hUI : MemLp (fun w => U w Complex.I) 2 (volume.restrict (annulusSet a b))) :
    MemLp (radialField U) 2 (volume.restrict (annulusSet a b)) := by
  have hwre : AEStronglyMeasurable (fun z : ℂ => z.re / ‖z‖)
      (volume.restrict (annulusSet a b)) := by
    refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_annulusSet
    intro z hz
    have hz0 : ‖z‖ ≠ 0 := ne_of_gt (lt_trans ha hz.1)
    exact ((Complex.continuous_re.continuousAt).continuousWithinAt.div
      (continuous_norm.continuousAt).continuousWithinAt hz0)
  have hwim : AEStronglyMeasurable (fun z : ℂ => z.im / ‖z‖)
      (volume.restrict (annulusSet a b)) := by
    refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_annulusSet
    intro z hz
    have hz0 : ‖z‖ ≠ 0 := ne_of_gt (lt_trans ha hz.1)
    exact ((Complex.continuous_im.continuousAt).continuousWithinAt.div
      (continuous_norm.continuousAt).continuousWithinAt hz0)
  have habs : ∀ᵐ z ∂(volume.restrict (annulusSet a b)),
      |z.re / ‖z‖| ≤ 1 ∧ |z.im / ‖z‖| ≤ 1 := by
    filter_upwards [ae_restrict_mem measurableSet_annulusSet] with z hz
    have hz0 : (0 : ℝ) < ‖z‖ := lt_trans ha hz.1
    constructor
    · rw [abs_div, abs_of_pos hz0, div_le_one hz0]
      exact Complex.abs_re_le_norm z
    · rw [abs_div, abs_of_pos hz0, div_le_one hz0]
      exact Complex.abs_im_le_norm z
  have hterm1 : MemLp (fun z => (z.re / ‖z‖) • U z 1) 2
      (volume.restrict (annulusSet a b)) := by
    rw [memLp_iff]
    refine lt_of_le_of_lt (eLpNorm_mono_ae (hwre.smul hU1.aestronglyMeasurable) ?_) hU1.eLpNorm_lt_top
    filter_upwards [habs] with z hz
    rw [norm_smul, Real.norm_eq_abs]
    exact mul_le_of_le_one_left (norm_nonneg _) hz.1
  have hterm2 : MemLp (fun z => (z.im / ‖z‖) • U z Complex.I) 2
      (volume.restrict (annulusSet a b)) := by
    rw [memLp_iff]
    refine lt_of_le_of_lt (eLpNorm_mono_ae (hwim.smul hUI.aestronglyMeasurable) ?_) hUI.eLpNorm_lt_top
    filter_upwards [habs] with z hz
    rw [norm_smul, Real.norm_eq_abs]
    exact mul_le_of_le_one_left (norm_nonneg _) hz.2
  exact hterm1.add hterm2

end SliceMeasurability

section Contracts

variable {a b : ℝ}

/-- **A.e.-invariance**: the radial Bochner map depends only on the
a.e.-class of the input on the annulus. -/
theorem sliceLp_congr_ae (ha : 0 < a) {u u' : ℂ → ℂ}
    (h : u =ᵐ[volume.restrict (annulusSet a b)] u') :
    ∀ᵐ t ∂(volume.restrict (Ioo a b)), sliceLp a b u t = sliceLp a b u' t := by
  filter_upwards [ae_slice_ae_eq ha h, ae_restrict_mem measurableSet_Ioo]
    with t heq htI
  by_cases hm : MemLp (sliceFun u t) 2 circleMeasure
  · have hm' : MemLp (sliceFun u' t) 2 circleMeasure := hm.ae_eq heq
    rw [sliceLp_of_memLp htI hm, sliceLp_of_memLp htI hm']
    exact MemLp.toLp_congr hm hm' heq
  · have hm' : ¬MemLp (sliceFun u' t) 2 circleMeasure :=
      fun h' => hm (h'.ae_eq heq.symm)
    rw [sliceLp, sliceLp]
    split
    · next hc => exact absurd hc.2 hm
    · next _ =>
      split
      · next hc => exact absurd hc.2 hm'
      · next _ => rfl

/-- **Exact weighted norm identity** (ENNReal form): the annulus square integral
IS the radially weighted square of the Bochner map — the genuine area Jacobian,
an identity, not a bound. -/
theorem lintegral_annulus_eq_weighted_sliceLp (ha : 0 < a) {u : ℂ → ℂ}
    (hu : MemLp u 2 (volume.restrict (annulusSet a b))) :
    ∫⁻ w in annulusSet a b, ‖u w‖ₑ ^ (2 : ℕ)
      = ∫⁻ t in Ioo a b, ENNReal.ofReal t * ‖sliceLp a b u t‖ₑ ^ (2 : ℕ) := by
  obtain ⟨v, hv, huv⟩ := hu.aestronglyMeasurable
  have hvr : MemLp v 2 (volume.restrict (annulusSet a b)) := hu.ae_eq huv
  have hleft : (∫⁻ w in annulusSet a b, ‖u w‖ₑ ^ (2 : ℕ))
      = ∫⁻ w in annulusSet a b, ‖v w‖ₑ ^ (2 : ℕ) := by
    refine lintegral_congr_ae ?_
    filter_upwards [huv] with w hw
    rw [hw]
  rw [hleft, lintegral_annulus_sq (b := b) ha hv.measurable]
  refine lintegral_congr_ae ?_
  filter_upwards [ae_slice_ae_eq ha huv, ae_sliceFun_memLp ha hu,
    ae_restrict_mem measurableSet_Ioo] with t heq hm htI
  congr 1
  have hinner : (∫⁻ w, ‖sliceFun v t w‖ₑ ^ (2 : ℕ) ∂circleMeasure)
      = ∫⁻ w, ‖sliceFun u t w‖ₑ ^ (2 : ℕ) ∂circleMeasure := by
    refine lintegral_congr_ae ?_
    filter_upwards [heq] with w hw
    rw [hw]
  rw [hinner, sliceLp_of_memLp htI hm, Lp.enorm_toLp,
    eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num : (2 : ℝ≥0∞) ≠ 0)
      (by norm_num : (2 : ℝ≥0∞) ≠ ∞) hm.aestronglyMeasurable]
  have htr : ((2 : ℝ≥0∞)).toReal = ((2 : ℕ) : ℝ) := by norm_num
  rw [htr, ← ENNReal.rpow_natCast
    ((∫⁻ w, ‖sliceFun u t w‖ₑ ^ (((2 : ℕ) : ℝ)) ∂circleMeasure)
      ^ (1 / ((2 : ℕ) : ℝ))) 2, ← ENNReal.rpow_mul]
  norm_num

/-- **Two-sided comparison**: the weight is bounded between the
radii. -/
theorem le_lintegral_annulus (ha : 0 < a) {u : ℂ → ℂ}
    (hu : MemLp u 2 (volume.restrict (annulusSet a b))) :
    ENNReal.ofReal a * (∫⁻ t in Ioo a b, ‖sliceLp a b u t‖ₑ ^ (2 : ℕ))
        ≤ ∫⁻ w in annulusSet a b, ‖u w‖ₑ ^ (2 : ℕ) ∧
      (∫⁻ w in annulusSet a b, ‖u w‖ₑ ^ (2 : ℕ))
        ≤ ENNReal.ofReal b * ∫⁻ t in Ioo a b, ‖sliceLp a b u t‖ₑ ^ (2 : ℕ) := by
  have hmeas : AEMeasurable (fun t : ℝ => ‖sliceLp a b u t‖ₑ ^ (2 : ℕ))
      (volume.restrict (Ioo a b)) :=
    ((aestronglyMeasurable_sliceLp ha hu).enorm.pow_const 2)
  rw [lintegral_annulus_eq_weighted_sliceLp ha hu]
  constructor
  · rw [← lintegral_const_mul'' _ hmeas]
    refine setLIntegral_mono_ae ((ENNReal.measurable_ofReal.comp
      measurable_id).aemeasurable.mul hmeas) ?_
    filter_upwards with t htI
    exact mul_le_mul' (ENNReal.ofReal_le_ofReal htI.1.le) le_rfl
  · rw [← lintegral_const_mul'' _ hmeas]
    refine setLIntegral_mono_ae ((measurable_const.aemeasurable.mul hmeas)) ?_
    filter_upwards with t htI
    exact mul_le_mul' (ENNReal.ofReal_le_ofReal htI.2.le) le_rfl

/-- **Radial energy bound** (no reverse bound is asserted): the
radial field's density is dominated by twice the full directional density. -/
lemma enorm_radialField_sq_le (ha : 0 < a) (U : ℂ → ℂ →L[ℝ] ℂ) :
    ∀ᵐ z ∂(volume.restrict (annulusSet a b)),
      ‖radialField U z‖ₑ ^ (2 : ℕ)
        ≤ 2 * (‖U z 1‖ₑ ^ (2 : ℕ) + ‖U z Complex.I‖ₑ ^ (2 : ℕ)) := by
  filter_upwards [ae_restrict_mem measurableSet_annulusSet] with z hz
  have hz0 : (0 : ℝ) < ‖z‖ := lt_trans ha hz.1
  have hre : |z.re / ‖z‖| ≤ 1 := by
    rw [abs_div, abs_of_pos hz0, div_le_one hz0]
    exact Complex.abs_re_le_norm z
  have him : |z.im / ‖z‖| ≤ 1 := by
    rw [abs_div, abs_of_pos hz0, div_le_one hz0]
    exact Complex.abs_im_le_norm z
  have hreal : ‖radialField U z‖ ^ (2 : ℕ)
      ≤ 2 * (‖U z 1‖ ^ (2 : ℕ) + ‖U z Complex.I‖ ^ (2 : ℕ)) := by
    have h1 : ‖radialField U z‖ ≤ ‖U z 1‖ + ‖U z Complex.I‖ := by
      refine le_trans (norm_add_le _ _) ?_
      gcongr
      · rw [norm_smul, Real.norm_eq_abs]
        exact mul_le_of_le_one_left (norm_nonneg _) hre
      · rw [norm_smul, Real.norm_eq_abs]
        exact mul_le_of_le_one_left (norm_nonneg _) him
    nlinarith [norm_nonneg (radialField U z), norm_nonneg (U z 1),
      norm_nonneg (U z Complex.I), sq_nonneg (‖U z 1‖ - ‖U z Complex.I‖)]
  calc ‖radialField U z‖ₑ ^ (2 : ℕ)
      = ENNReal.ofReal (‖radialField U z‖ ^ (2 : ℕ)) := by
        rw [← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _)]
    _ ≤ ENNReal.ofReal (2 * (‖U z 1‖ ^ (2 : ℕ) + ‖U z Complex.I‖ ^ (2 : ℕ))) :=
        ENNReal.ofReal_le_ofReal hreal
    _ = 2 * (‖U z 1‖ₑ ^ (2 : ℕ) + ‖U z Complex.I‖ₑ ^ (2 : ℕ)) := by
        rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_add (by positivity)
          (by positivity), ENNReal.ofReal_pow (norm_nonneg _),
          ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm,
          ofReal_norm]
        norm_num

end Contracts

section RadialCalculus

open ContinuousLinearMap

/-- The norm's derivative on `ℂ ∖ {0}` (real inner-product route). -/
lemma hasFDerivAt_norm' {z : ℂ} (hz : z ≠ 0) :
    HasFDerivAt (fun w : ℂ => ‖w‖) (‖z‖⁻¹ • innerSL ℝ z) z := by
  have h1 : HasFDerivAt (fun w : ℂ => ‖w‖ ^ 2) (2 • innerSL ℝ z) z :=
    (hasStrictFDerivAt_norm_sq z).hasFDerivAt
  have hq : ‖z‖ ^ 2 ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.mpr hz)
  have h2 : HasDerivAt Real.sqrt (1 / (2 * Real.sqrt (‖z‖ ^ 2))) (‖z‖ ^ 2) :=
    Real.hasDerivAt_sqrt hq
  have h3 := h2.comp_hasFDerivAt z h1
  have hfun : Real.sqrt ∘ (fun w : ℂ => ‖w‖ ^ 2) = fun w : ℂ => ‖w‖ := by
    funext w
    exact Real.sqrt_sq (norm_nonneg w)
  rw [hfun] at h3
  have hclm : (1 / (2 * Real.sqrt (‖z‖ ^ 2))) • (2 • innerSL ℝ z)
      = ‖z‖⁻¹ • innerSL ℝ z := by
    ext v
    simp only [smul_apply, innerSL_apply_apply, smul_eq_mul, nsmul_eq_mul,
      Nat.cast_ofNat, Real.sqrt_sq (norm_nonneg z)]
    have hnz : ‖z‖ ≠ 0 := norm_ne_zero_iff.mpr hz
    field_simp
  rwa [hclm] at h3

/-- The unit (degree-zero) direction map. -/
def nUnit (z : ℂ) : ℂ := ‖z‖⁻¹ • z

lemma nUnit_of_circle (t : ℝ) (ht : 0 < t) (w : Circle₁) :
    nUnit (t • (w : ℂ)) = (w : ℂ) := by
  have hw : ‖(w : ℂ)‖ = 1 := mem_sphere_zero_iff_norm.mp w.property
  rw [nUnit, norm_smul, Real.norm_eq_abs, hw, mul_one, abs_of_pos ht,
    smul_smul, inv_mul_cancel₀ (ne_of_gt ht), one_smul]

/-- The inverse norm's derivative. -/
lemma hasFDerivAt_invNorm {z : ℂ} (hz : z ≠ 0) :
    HasFDerivAt (fun w : ℂ => ‖w‖⁻¹) ((-(‖z‖⁻¹ ^ 2) * ‖z‖⁻¹) • innerSL ℝ z) z := by
  have hnz : ‖z‖ ≠ 0 := norm_ne_zero_iff.mpr hz
  have hinv : HasDerivAt (fun y : ℝ => y⁻¹) (-(‖z‖ ^ 2)⁻¹) ‖z‖ :=
    hasDerivAt_inv hnz
  have h := hinv.comp_hasFDerivAt z (hasFDerivAt_norm' hz)
  have hfun : (fun y : ℝ => y⁻¹) ∘ (fun w : ℂ => ‖w‖)
      = fun w : ℂ => ‖w‖⁻¹ := rfl
  rw [hfun] at h
  have hclm : (-(‖z‖ ^ 2)⁻¹) • (‖z‖⁻¹ • innerSL ℝ z)
      = (-(‖z‖⁻¹ ^ 2) * ‖z‖⁻¹) • innerSL ℝ z := by
    rw [smul_smul]
    congr 1
    ring
  rwa [hclm] at h

/-- The unit map's derivative, in the product-rule canonical shape. -/
lemma hasFDerivAt_nUnit {z : ℂ} (hz : z ≠ 0) :
    HasFDerivAt nUnit
      (‖z‖⁻¹ • ContinuousLinearMap.id ℝ ℂ
        + ((-(‖z‖⁻¹ ^ 2) * ‖z‖⁻¹) • innerSL ℝ z).smulRight z) z := by
  have h := (hasFDerivAt_invNorm hz).smul (hasFDerivAt_id z)
  exact h

/-- **Euler's identity for the unit map**: its radial derivative vanishes. -/
lemma fderiv_nUnit_radial {z : ℂ} (hz : z ≠ 0) :
    (‖z‖⁻¹ • ContinuousLinearMap.id ℝ ℂ
      + ((-(‖z‖⁻¹ ^ 2) * ‖z‖⁻¹) • innerSL ℝ z).smulRight z) z = 0 := by
  simp only [add_apply, smul_apply, ContinuousLinearMap.id_apply,
    smulRight_apply, innerSL_apply_apply, real_inner_self_eq_norm_sq,
    smul_eq_mul]
  have hnz : ‖z‖ ≠ 0 := norm_ne_zero_iff.mpr hz
  have hcoef : -(‖z‖⁻¹ ^ 2) * ‖z‖⁻¹ * ‖z‖ ^ 2 = -‖z‖⁻¹ := by
    field_simp
  rw [hcoef, neg_smul, add_neg_cancel]

end RadialCalculus

section PsiTests

open ContinuousLinearMap

variable {φ : ℝ → ℝ} {H : ℂ → ℝ}

/-- The angular extension obtained by evaluating `H` on the normalized direction.
It is constant along positive radial rays away from the origin. -/
def angExt (H : ℂ → ℝ) : ℂ → ℝ := fun z => H (nUnit z)

/-- The 2-D weak test in direction `e`: radial profile × direction cosine ×
degree-zero angular factor. -/
def psiTest (φ : ℝ → ℝ) (H : ℂ → ℝ) (e : ℂ) : ℂ → ℝ :=
  fun z => φ ‖z‖ * (inner ℝ (nUnit z) e * angExt H z)

/-- The real inner product on `ℂ` in coordinates. -/
lemma real_inner_complex (x y : ℂ) :
    (inner ℝ x y : ℝ) = x.re * y.re + x.im * y.im := by
  rw [real_inner_eq_re_inner (𝕜 := ℂ)]
  simp only [RCLike.inner_apply, RCLike.re_to_complex, Complex.mul_re,
    Complex.conj_re, Complex.conj_im]
  ring

/-- The per-direction derivative package, in the product-rule canonical shape. -/
lemma hasFDerivAt_psiTest (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hH : ContDiff ℝ (⊤ : ℕ∞) H) (e : ℂ) {z : ℂ} (hz : z ≠ 0) :
    HasFDerivAt (psiTest φ H e)
      (φ ‖z‖ •
          ((inner ℝ (nUnit z) e) •
              ((fderiv ℝ H (nUnit z)).comp
                (‖z‖⁻¹ • ContinuousLinearMap.id ℝ ℂ
                  + ((-(‖z‖⁻¹ ^ 2) * ‖z‖⁻¹) • innerSL ℝ z).smulRight z))
            + (angExt H z) •
              ((innerSL ℝ e).comp
                (‖z‖⁻¹ • ContinuousLinearMap.id ℝ ℂ
                  + ((-(‖z‖⁻¹ ^ 2) * ‖z‖⁻¹) • innerSL ℝ z).smulRight z)))
        + (inner ℝ (nUnit z) e * angExt H z) •
            (deriv φ ‖z‖ • (‖z‖⁻¹ • innerSL ℝ z))) z := by
  have hn := hasFDerivAt_nUnit hz
  have h1 : HasFDerivAt (fun w : ℂ => φ ‖w‖)
      (deriv φ ‖z‖ • (‖z‖⁻¹ • innerSL ℝ z)) z := by
    have hd : HasDerivAt φ (deriv φ ‖z‖) ‖z‖ :=
      ((contDiff_infty_iff_deriv.mp hφ).1 ‖z‖).hasDerivAt
    exact hd.comp_hasFDerivAt z (hasFDerivAt_norm' hz)
  have h2 : HasFDerivAt (fun w : ℂ => inner ℝ (nUnit w) e)
      ((innerSL ℝ e).comp
        (‖z‖⁻¹ • ContinuousLinearMap.id ℝ ℂ
          + ((-(‖z‖⁻¹ ^ 2) * ‖z‖⁻¹) • innerSL ℝ z).smulRight z)) z := by
    have hswap : (fun w : ℂ => inner ℝ (nUnit w) e)
        = fun w : ℂ => (innerSL ℝ e) (nUnit w) := by
      funext w
      rw [innerSL_apply_apply, real_inner_comm]
    rw [hswap]
    exact ((innerSL ℝ e).hasFDerivAt).comp z hn
  have h3 : HasFDerivAt (angExt H)
      ((fderiv ℝ H (nUnit z)).comp
        (‖z‖⁻¹ • ContinuousLinearMap.id ℝ ℂ
          + ((-(‖z‖⁻¹ ^ 2) * ‖z‖⁻¹) • innerSL ℝ z).smulRight z)) z := by
    have hHd : HasFDerivAt H (fderiv ℝ H (nUnit z)) (nUnit z) :=
      (hH.differentiable (by simp)).differentiableAt.hasFDerivAt
    exact hHd.comp z hn
  exact h1.mul (h2.mul h3)

/-- Summing the directional derivatives of the two tests in their respective
basis directions produces the radial divergence form
`(φ′(r) + φ(r)/r)·ĥ` — the Euler mechanism kills the angular atoms and the
basis identities collapse the rest. -/
lemma psiTest_directional_sum (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hH : ContDiff ℝ (⊤ : ℕ∞) H) {z : ℂ} (hz : z ≠ 0) :
    lineDeriv ℝ (psiTest φ H 1) z 1
        + lineDeriv ℝ (psiTest φ H Complex.I) z Complex.I
      = (deriv φ ‖z‖ + φ ‖z‖ * ‖z‖⁻¹) * angExt H z := by
  have hnz : ‖z‖ ≠ 0 := norm_ne_zero_iff.mpr hz
  have hA := ((hasFDerivAt_psiTest hφ hH 1 hz).hasLineDerivAt 1).lineDeriv
  have hB := ((hasFDerivAt_psiTest hφ hH Complex.I hz).hasLineDerivAt
    Complex.I).lineDeriv
  rw [hA, hB]
  -- decompose the opaque angular derivative through the real basis {1, I}
  set A : ℝ := (fderiv ℝ H (nUnit z)) 1 with hAdef
  set B : ℝ := (fderiv ℝ H (nUnit z)) Complex.I with hBdef
  have hzdec : (fderiv ℝ H (nUnit z)) z = z.re * A + z.im * B := by
    have hz' : z = z.re • (1 : ℂ) + z.im • Complex.I := by
      rw [Complex.real_smul, Complex.real_smul, mul_one, Complex.re_add_im]
    rw [hAdef, hBdef, ← smul_eq_mul, ← smul_eq_mul,
      ← (fderiv ℝ H (nUnit z)).map_smul, ← (fderiv ℝ H (nUnit z)).map_smul,
      ← (fderiv ℝ H (nUnit z)).map_add, ← hz']
  -- the unit-map coordinates, without unfolding `nUnit` under the atoms
  have hnre : (nUnit z).re = ‖z‖⁻¹ * z.re := by
    rw [nUnit, Complex.real_smul, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im]
    ring
  have hnim : (nUnit z).im = ‖z‖⁻¹ * z.im := by
    rw [nUnit, Complex.real_smul, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im]
    ring
  -- expand every application into coordinates
  simp only [add_apply, smul_apply, coe_comp, Function.comp_apply,
    ContinuousLinearMap.id_apply, smulRight_apply, innerSL_apply_apply,
    smul_eq_mul, map_add, map_smul, hzdec]
  simp only [real_inner_complex, hnre, hnim,
    Complex.one_re, Complex.one_im, Complex.I_re, Complex.I_im]
  rw [← hAdef, ← hBdef]
  have hsq : z.re * z.re + z.im * z.im = ‖z‖ * ‖z‖ := by
    have h := Complex.normSq_eq_norm_sq z
    rw [Complex.normSq_apply] at h
    rw [h]
    ring
  field_simp
  ring_nf
  linear_combination (-(φ ‖z‖) * z.re * A - (φ ‖z‖) * z.im * B
    - (φ ‖z‖) * ‖z‖ * angExt H z + ‖z‖ ^ 2 * angExt H z * deriv φ ‖z‖) * hsq

/-- The tests are globally smooth: smooth off the origin by composition, and
identically zero near the origin because the radial profile's support starts
at `a > 0`. -/
lemma contDiff_psiTest {a b : ℝ} (ha : 0 < a) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hφs : tsupport φ ⊆ Ioo a b) (hH : ContDiff ℝ (⊤ : ℕ∞) H) (e : ℂ) :
    ContDiff ℝ (⊤ : ℕ∞) (psiTest φ H e) := by
  rw [contDiff_iff_contDiffAt]
  intro z
  by_cases hz : z = 0
  · subst hz
    have hzero : ∀ w ∈ Metric.ball (0 : ℂ) a, psiTest φ H e w = 0 := by
      intro w hw
      rw [Metric.mem_ball, dist_zero_right] at hw
      have hφ0 : φ ‖w‖ = 0 :=
        image_eq_zero_of_notMem_tsupport
          (fun hmem => absurd (hφs hmem).1 (not_lt.mpr hw.le))
      rw [psiTest, hφ0, zero_mul]
    refine (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq ?_
    filter_upwards [Metric.ball_mem_nhds (0 : ℂ) ha] with w hw
    exact hzero w hw
  · have hnorm : ContDiffAt ℝ (⊤ : ℕ∞) (fun w : ℂ => ‖w‖) z :=
      contDiffAt_norm ℝ hz
    have hnU : ContDiffAt ℝ (⊤ : ℕ∞) nUnit z := by
      have hinv : ContDiffAt ℝ (⊤ : ℕ∞) (fun w : ℂ => ‖w‖⁻¹) z :=
        hnorm.inv (norm_ne_zero_iff.mpr hz)
      exact hinv.smul contDiffAt_id
    have h1 : ContDiffAt ℝ (⊤ : ℕ∞) (fun w : ℂ => φ ‖w‖) z :=
      hφ.contDiffAt.comp z hnorm
    have h2 : ContDiffAt ℝ (⊤ : ℕ∞) (fun w : ℂ => inner ℝ (nUnit w) e) z := by
      have hswap : (fun w : ℂ => inner ℝ (nUnit w) e)
          = fun w : ℂ => (innerSL ℝ e) (nUnit w) := by
        funext w
        rw [innerSL_apply_apply, real_inner_comm]
      rw [hswap]
      exact ((innerSL ℝ e).contDiff.contDiffAt).comp z hnU
    have h3 : ContDiffAt ℝ (⊤ : ℕ∞) (angExt H) z :=
      hH.contDiffAt.comp z hnU
    exact h1.mul (h2.mul h3)

/-- The topological support of each test lies inside the open annulus. -/
lemma tsupport_psiTest_subset {a b : ℝ} {e : ℂ}
    (hφs : tsupport φ ⊆ Ioo a b) :
    tsupport (psiTest φ H e) ⊆ annulusSet a b := by
  have hsupp : Function.support (psiTest φ H e)
      ⊆ (fun z : ℂ => ‖z‖) ⁻¹' tsupport φ := by
    intro z hzs
    by_contra hmem
    apply hzs
    rw [psiTest, image_eq_zero_of_notMem_tsupport hmem, zero_mul]
  refine (closure_minimal hsupp
    (IsClosed.preimage continuous_norm isClosed_closure)).trans ?_
  intro z hzp
  exact hφs hzp

lemma hasCompactSupport_psiTest {a b : ℝ} {e : ℂ} (hφc : HasCompactSupport φ)
    (_hφs : tsupport φ ⊆ Ioo a b) :
    HasCompactSupport (psiTest φ H e) := by
  obtain ⟨M, hM⟩ := hφc.isBounded.subset_closedBall 0
  have hsub : tsupport (psiTest φ H e) ⊆ Metric.closedBall (0 : ℂ) M := by
    have h1 : Function.support (psiTest φ H e)
        ⊆ (fun z : ℂ => ‖z‖) ⁻¹' tsupport φ := by
      intro z hzs
      by_contra hmem
      apply hzs
      rw [psiTest, image_eq_zero_of_notMem_tsupport hmem, zero_mul]
    refine (closure_minimal h1
      (IsClosed.preimage continuous_norm isClosed_closure)).trans ?_
    intro z hz
    have := hM hz
    rw [Metric.mem_closedBall, dist_zero_right] at this ⊢
    rwa [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg z)] at this
  exact HasCompactSupport.intro (isCompact_closedBall 0 M)
    (fun z hz => image_eq_zero_of_notMem_tsupport (fun hmem => hz (hsub hmem)))

/-- The radial profile vanishes at and near the origin. -/
lemma phi_norm_zero_near_zero {a b : ℝ} (ha : 0 < a)
    (hφs : tsupport φ ⊆ Ioo a b) :
    φ 0 = 0 ∧ deriv φ 0 = 0 := by
  have hev : φ =ᶠ[𝓝 (0 : ℝ)] fun _ => (0 : ℝ) := by
    filter_upwards [Metric.ball_mem_nhds (0 : ℝ) ha] with x hx
    rw [Metric.mem_ball, Real.dist_eq, sub_zero] at hx
    exact image_eq_zero_of_notMem_tsupport
      (fun hmem => absurd (hφs hmem).1 (not_lt.mpr ((le_abs_self x).trans hx.le)))
  constructor
  · exact hev.self_of_nhds
  · rw [hev.deriv_eq]
    exact deriv_const 0 0

/-- Testing the planar weak derivative identity in directions `1` and `I`
and adding gives the radial divergence pairing. The angular derivative terms
cancel by `psiTest_directional_sum`. -/
lemma weak_radial_identity {a b : ℝ} (ha : 0 < a) {u : ℂ → ℂ}
    {U : ℂ → ℂ →L[ℝ] ℂ}
    (hweak : TauCeti.HasWeakFDerivOn volume (annulusOpens a b) u U)
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hφc : HasCompactSupport φ)
    (hφs : tsupport φ ⊆ Ioo a b) (hH : ContDiff ℝ (⊤ : ℕ∞) H) :
    (∫ z, ((deriv φ ‖z‖ + φ ‖z‖ * ‖z‖⁻¹) * angExt H z) • u z)
      = -∫ z, (φ ‖z‖ * angExt H z) • radialField U z := by
  have hw1 := hweak.hasWeakLineDerivOn 1
  have hwI := hweak.hasWeakLineDerivOn Complex.I
  set ψ₁ : 𝓓(annulusOpens a b, ℝ) :=
    ⟨psiTest φ H 1, contDiff_psiTest ha hφ hφs hH 1,
      hasCompactSupport_psiTest hφc hφs, tsupport_psiTest_subset hφs⟩ with hψ₁
  set ψ₂ : 𝓓(annulusOpens a b, ℝ) :=
    ⟨psiTest φ H Complex.I, contDiff_psiTest ha hφ hφs hH Complex.I,
      hasCompactSupport_psiTest hφc hφs, tsupport_psiTest_subset hφs⟩ with hψ₂
  have hid1 := hw1.integral_lineDeriv_smul_eq_neg_integral_smul ψ₁
  have hidI := hwI.integral_lineDeriv_smul_eq_neg_integral_smul ψ₂
  have hint1 := TauCeti.integrable_lineDeriv_smul_of_locallyIntegrableOn
    hw1.locallyIntegrableOn ψ₁ 1
  have hintI := TauCeti.integrable_lineDeriv_smul_of_locallyIntegrableOn
    hwI.locallyIntegrableOn ψ₂ Complex.I
  have hintR1 := TauCeti.integrable_smul_of_locallyIntegrableOn
    hw1.locallyIntegrableOn_deriv ψ₁
  have hintRI := TauCeti.integrable_smul_of_locallyIntegrableOn
    hwI.locallyIntegrableOn_deriv ψ₂
  have hsum : (∫ z, (lineDeriv ℝ (ψ₁ : ℂ → ℝ) z 1 • u z
        + lineDeriv ℝ (ψ₂ : ℂ → ℝ) z Complex.I • u z))
      = -∫ z, ((ψ₁ : ℂ → ℝ) z • U z 1 + (ψ₂ : ℂ → ℝ) z • U z Complex.I) := by
    rw [MeasureTheory.integral_add hint1 hintI,
      MeasureTheory.integral_add hintR1 hintRI, hid1, hidI, neg_add]
  have hzero_t : (0 : ℂ) ∉ tsupport (psiTest φ H (1 : ℂ)) ∧
      (0 : ℂ) ∉ tsupport (psiTest φ H Complex.I) := by
    constructor <;>
      exact fun hmem => by
        have := tsupport_psiTest_subset hφs hmem
        rw [mem_annulusSet] at this
        simp only [norm_zero] at this
        exact absurd this.1 (not_lt.mpr ha.le)
  have hc1 : ((ψ₁ : 𝓓(annulusOpens a b, ℝ)) : ℂ → ℝ) = psiTest φ H 1 := rfl
  have hc2 : ((ψ₂ : 𝓓(annulusOpens a b, ℝ)) : ℂ → ℝ)
      = psiTest φ H Complex.I := rfl
  have hLHS : (∫ z, (lineDeriv ℝ (ψ₁ : ℂ → ℝ) z 1 • u z
        + lineDeriv ℝ (ψ₂ : ℂ → ℝ) z Complex.I • u z))
      = ∫ z, ((deriv φ ‖z‖ + φ ‖z‖ * ‖z‖⁻¹) * angExt H z) • u z := by
    refine MeasureTheory.integral_congr_ae ?_
    filter_upwards with z
    by_cases hz : z = 0
    · subst hz
      rw [TauCeti.lineDeriv_eq_zero_of_notMem_tsupport ψ₁ hzero_t.1 1,
        TauCeti.lineDeriv_eq_zero_of_notMem_tsupport ψ₂ hzero_t.2 Complex.I]
      obtain ⟨h0, hd0⟩ := phi_norm_zero_near_zero ha hφs
      simp only [norm_zero, h0, hd0, zero_mul, mul_zero, add_zero,
        zero_smul, inv_zero]
    · rw [hc1, hc2, ← add_smul, psiTest_directional_sum hφ hH hz]
  have hRHS : (∫ z, ((ψ₁ : ℂ → ℝ) z • U z 1 + (ψ₂ : ℂ → ℝ) z • U z Complex.I))
      = ∫ z, (φ ‖z‖ * angExt H z) • radialField U z := by
    refine MeasureTheory.integral_congr_ae ?_
    filter_upwards with z
    rw [show (ψ₁ : ℂ → ℝ) z = psiTest φ H 1 z from congrFun hc1 z,
      show (ψ₂ : ℂ → ℝ) z = psiTest φ H Complex.I z from congrFun hc2 z]
    by_cases hz : z = 0
    · subst hz
      obtain ⟨h0, _⟩ := phi_norm_zero_near_zero ha hφs
      rw [image_eq_zero_of_notMem_tsupport hzero_t.1,
        image_eq_zero_of_notMem_tsupport hzero_t.2]
      simp only [norm_zero, h0, zero_mul, zero_smul, add_zero]
    · have hnz : ‖z‖ ≠ 0 := norm_ne_zero_iff.mpr hz
      simp only [psiTest, radialField]
      rw [real_inner_complex, real_inner_complex]
      have hnre : (nUnit z).re = ‖z‖⁻¹ * z.re := by
        rw [nUnit, Complex.real_smul, Complex.mul_re, Complex.ofReal_re,
          Complex.ofReal_im]
        ring
      have hnim : (nUnit z).im = ‖z‖⁻¹ * z.im := by
        rw [nUnit, Complex.real_smul, Complex.mul_im, Complex.ofReal_re,
          Complex.ofReal_im]
        ring
      simp only [hnre, hnim, Complex.one_re, Complex.one_im, Complex.I_re,
        Complex.I_im, mul_zero, mul_one, add_zero, zero_add, smul_add,
        smul_smul]
      congr 1
      · congr 1
        field_simp
      · congr 1
        field_simp
  rw [hLHS] at hsum
  rw [hRHS] at hsum
  exact hsum

end PsiTests

section MeasureFactorization

variable {a b : ℝ}

/-- **The measure-level polar factorization**: the radially weighted product of
the interval measure with σ pushes forward under the scaling map to exactly the
annulus measure.  Every Bochner change of variables below is `integral_map` on
this one identity. -/
lemma map_polarMul_withDensity (ha : 0 < a) :
    Measure.map polarMul
        (((volume.restrict (Ioo a b)).prod circleMeasure).withDensity
          (fun p => ENNReal.ofReal p.1))
      = volume.restrict (annulusSet a b) := by
  refine Measure.ext (fun S hS => ?_)
  rw [Measure.map_apply measurable_polarMul hS,
    withDensity_apply _ (measurable_polarMul hS)]
  have hind : (∫⁻ p in polarMul ⁻¹' S, ENNReal.ofReal p.1
        ∂((volume.restrict (Ioo a b)).prod circleMeasure))
      = ∫⁻ p, (polarMul ⁻¹' S).indicator (fun p : ℝ × Circle₁ =>
          ENNReal.ofReal p.1) p
        ∂((volume.restrict (Ioo a b)).prod circleMeasure) := by
    rw [lintegral_indicator (measurable_polarMul hS)]
  rw [hind, MeasureTheory.lintegral_prod _ ((measurable_fst.ennreal_ofReal).indicator
    (measurable_polarMul hS)).aemeasurable]
  have hslice : ∀ t : ℝ,
      (∫⁻ w, (polarMul ⁻¹' S).indicator
          (fun p : ℝ × Circle₁ => ENNReal.ofReal p.1) (t, w) ∂circleMeasure)
        = ENNReal.ofReal t * ∫⁻ w, S.indicator 1 (t • (w : ℂ)) ∂circleMeasure := by
    intro t
    have hsm : Measurable fun w : Circle₁ =>
        S.indicator (1 : ℂ → ℝ≥0∞) (t • (w : ℂ)) := by
      apply (measurable_one.indicator hS).comp
      apply Continuous.measurable
      exact (continuous_const : Continuous fun _ : Circle₁ => t).smul
        (continuous_subtype_val : Continuous fun w : Circle₁ => (w : ℂ))
    rw [← lintegral_const_mul _ hsm]
    refine lintegral_congr (fun w => ?_)
    by_cases hw : t • (w : ℂ) ∈ S
    · rw [Set.indicator_of_mem (by exact hw), Set.indicator_of_mem hw]
      simp
    · rw [Set.indicator_of_notMem (by exact hw), Set.indicator_of_notMem hw]
      simp
  rw [lintegral_congr (fun t => hslice t)]
  have hmaster := lintegral_annulus_polar (b := b) ha
    (f := S.indicator 1) (measurable_one.indicator hS)
  rw [← hmaster, lintegral_indicator_one hS, Measure.restrict_apply hS]

/-- Bochner change of variables on the factorization: annulus integrals are
weighted radial-circle integrals. -/
lemma integral_annulus_eq_weighted {f : ℂ → ℂ}
    (ha : 0 < a)
    (hf : AEStronglyMeasurable f (volume.restrict (annulusSet a b))) :
    ∫ z in annulusSet a b, f z
      = ∫ p, p.1 • f (polarMul p)
          ∂((volume.restrict (Ioo a b)).prod circleMeasure) := by
  rw [← map_polarMul_withDensity (b := b) ha] at hf ⊢
  rw [MeasureTheory.integral_map measurable_polarMul.aemeasurable hf]
  have hw : (fun p : ℝ × Circle₁ => ENNReal.ofReal p.1)
      = fun p : ℝ × Circle₁ => ((p.1.toNNReal : ℝ≥0) : ℝ≥0∞) := rfl
  rw [hw, _root_.integral_withDensity_eq_integral_smul
    (measurable_fst.real_toNNReal) _]
  have haefst : ∀ᵐ p : ℝ × Circle₁
      ∂((volume.restrict (Ioo a b)).prod circleMeasure), p.1 ∈ Ioo a b := by
    rw [MeasureTheory.ae_iff]
    have hset : {p : ℝ × Circle₁ | ¬p.1 ∈ Ioo a b}
        = ((Ioo a b)ᶜ ×ˢ Set.univ : Set (ℝ × Circle₁)) := by
      ext p
      simp [Set.mem_prod]
    rw [hset, Measure.prod_prod, Measure.restrict_apply' measurableSet_Ioo,
      Set.compl_inter_self, measure_empty, zero_mul]
  refine MeasureTheory.integral_congr_ae ?_
  filter_upwards [haefst] with p hp
  have hpos : (0 : ℝ) ≤ p.1 := (lt_trans ha hp.1).le
  rw [NNReal.smul_def, Real.coe_toNNReal _ hpos]

end MeasureFactorization

section RadialTest

variable {a b : ℝ} {χ : ℝ → ℝ}

/-- The `χ/r` radial profile: the reparametrization that absorbs the polar
divergence term (legal because the support starts at `a > 0`). -/
def radialProfile (χ : ℝ → ℝ) : ℝ → ℝ := fun t => χ t / t

lemma radialProfile_smul (ha : 0 < a) (hχs : tsupport χ ⊆ Ioo a b) :
    (fun s : ℝ => s * radialProfile χ s) = χ := by
  funext s
  by_cases hs : s = 0
  · subst hs
    rw [radialProfile]
    have h0 : χ 0 = 0 :=
      image_eq_zero_of_notMem_tsupport
        (fun hmem => absurd (hχs hmem).1 (not_lt.mpr ha.le))
    rw [h0]
    simp
  · rw [radialProfile]
    field_simp

lemma contDiff_radialProfile (ha : 0 < a) (hχ : ContDiff ℝ (⊤ : ℕ∞) χ)
    (hχs : tsupport χ ⊆ Ioo a b) :
    ContDiff ℝ (⊤ : ℕ∞) (radialProfile χ) := by
  rw [contDiff_iff_contDiffAt]
  intro t
  by_cases ht : t = 0
  · subst ht
    have hzero : ∀ s ∈ Metric.ball (0 : ℝ) a, radialProfile χ s = 0 := by
      intro s hs
      rw [Metric.mem_ball, Real.dist_eq, sub_zero] at hs
      have h0 : χ s = 0 :=
        image_eq_zero_of_notMem_tsupport
          (fun hmem => absurd (hχs hmem).1
            (not_lt.mpr ((le_abs_self s).trans hs.le)))
      rw [radialProfile, h0, zero_div]
    refine (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq ?_
    filter_upwards [Metric.ball_mem_nhds (0 : ℝ) ha] with s hs
    exact hzero s hs
  · exact hχ.contDiffAt.div contDiffAt_id ht

lemma hasCompactSupport_radialProfile (hχc : HasCompactSupport χ) :
    HasCompactSupport (radialProfile χ) := by
  refine HasCompactSupport.intro hχc (fun t ht => ?_)
  rw [radialProfile, image_eq_zero_of_notMem_tsupport ht, zero_div]

lemma tsupport_radialProfile_subset (hχs : tsupport χ ⊆ Ioo a b) :
    tsupport (radialProfile χ) ⊆ Ioo a b := by
  refine (closure_minimal (fun t ht => ?_) isClosed_closure).trans hχs
  by_contra hmem
  apply ht
  rw [radialProfile, image_eq_zero_of_notMem_tsupport hmem, zero_div]

/-- The reparametrized weight equals the target test's derivative:
`t·φ′(t) + φ(t) = χ′(t)` for `φ = χ/t`, globally. -/
lemma radialProfile_weight (ha : 0 < a) (hχ : ContDiff ℝ (⊤ : ℕ∞) χ)
    (hχs : tsupport χ ⊆ Ioo a b) (t : ℝ) :
    t * deriv (radialProfile χ) t + radialProfile χ t = deriv χ t := by
  have hsm := contDiff_radialProfile ha hχ hχs
  have hdiff : DifferentiableAt ℝ (radialProfile χ) t :=
    (contDiff_infty_iff_deriv.mp hsm).1 t
  have hmul : HasDerivAt (fun s : ℝ => s * radialProfile χ s)
      (1 * radialProfile χ t + t * deriv (radialProfile χ) t) t :=
    (hasDerivAt_id t).mul hdiff.hasDerivAt
  rw [radialProfile_smul ha hχs] at hmul
  rw [hmul.deriv]
  ring

end RadialTest

section PairingTransfer

variable {a b : ℝ}

/-- Off its support, a function's derivative also vanishes. -/
lemma deriv_eq_zero_of_notMem_tsupport {φ : ℝ → ℝ} {t : ℝ}
    (ht : t ∉ tsupport φ) : deriv φ t = 0 := by
  have hev : φ =ᶠ[𝓝 t] fun _ => (0 : ℝ) := by
    filter_upwards [(isClosed_closure (s := Function.support φ)).isOpen_compl.mem_nhds
      ht] with s hs
    exact image_eq_zero_of_notMem_tsupport hs
  rw [hev.deriv_eq]
  exact deriv_const t 0

/-- The product measure sees only radii in the interval. -/
lemma ae_fst_mem_Ioo :
    ∀ᵐ p : ℝ × Circle₁
      ∂((volume.restrict (Ioo a b)).prod circleMeasure), p.1 ∈ Ioo a b := by
  rw [MeasureTheory.ae_iff]
  have hset : {p : ℝ × Circle₁ | ¬p.1 ∈ Ioo a b}
      = ((Ioo a b)ᶜ ×ˢ Set.univ : Set (ℝ × Circle₁)) := by
    ext p
    simp [Set.mem_prod]
  rw [hset, Measure.prod_prod, Measure.restrict_apply' measurableSet_Ioo,
    Set.compl_inter_self, measure_empty, zero_mul]

/-- Integrability transfers through the polar factorization, with the weight. -/
lemma integrable_weighted_pullback (ha : 0 < a) {g : ℂ → ℂ}
    (hg : IntegrableOn g (annulusSet a b) volume) :
    Integrable (fun p : ℝ × Circle₁ => p.1 • g (polarMul p))
      ((volume.restrict (Ioo a b)).prod circleMeasure) := by
  have hmap : Integrable g (Measure.map polarMul
      (((volume.restrict (Ioo a b)).prod circleMeasure).withDensity
        (fun p => ENNReal.ofReal p.1))) := by
    rw [map_polarMul_withDensity (b := b) ha]
    exact hg
  have hpull := (integrable_map_measure
    (by rw [map_polarMul_withDensity (b := b) ha]; exact hg.aestronglyMeasurable)
    measurable_polarMul.aemeasurable).mp hmap
  have hwd : Integrable (fun p : ℝ × Circle₁ =>
      (p.1.toNNReal : ℝ) • g (polarMul p))
      ((volume.restrict (Ioo a b)).prod circleMeasure) := by
    have hweq : (fun p : ℝ × Circle₁ => ENNReal.ofReal p.1)
        = fun p : ℝ × Circle₁ => ((p.1.toNNReal : ℝ≥0) : ℝ≥0∞) := rfl
    rw [hweq] at hpull
    exact (integrable_withDensity_iff_integrable_smul
      (measurable_fst.real_toNNReal)).mp hpull
  refine hwd.congr ?_
  filter_upwards [ae_fst_mem_Ioo (a := a) (b := b)] with p hp
  rw [Real.coe_toNNReal _ (lt_trans ha hp.1).le]

/-- A function bounded on the annulus times an `L²` function is integrable
there (`L² ⊆ L¹` on the finite-measure annulus). -/
lemma integrableOn_bdd_smul (_ha : 0 < a) (_hab : a < b) {S : ℂ → ℝ} {u : ℂ → ℂ}
    (hS : AEStronglyMeasurable S (volume.restrict (annulusSet a b)))
    {C : ℝ} (hSC : ∀ᵐ z ∂(volume.restrict (annulusSet a b)), |S z| ≤ C)
    (hu : MemLp u 2 (volume.restrict (annulusSet a b))) :
    IntegrableOn (fun z => S z • u z) (annulusSet a b) volume := by
  have hfin : IsFiniteMeasure (volume.restrict (annulusSet a b)) := by
    constructor
    rw [Measure.restrict_apply_univ]
    have hsub : annulusSet a b ⊆ Metric.closedBall (0 : ℂ) b := fun z hz =>
      Metric.mem_closedBall.mpr (by
        rw [dist_zero_right]
        exact (mem_annulusSet.mp hz).2.le)
    exact lt_of_le_of_lt (measure_mono hsub)
      (isCompact_closedBall (0 : ℂ) b).measure_lt_top
  have hu1 : Integrable u (volume.restrict (annulusSet a b)) := by
    rw [← MeasureTheory.memLp_one_iff_integrable]
    exact hu.mono_exponent (by norm_num)
  refine Integrable.mono' (hu1.norm.const_mul C)
    (hS.smul hu.aestronglyMeasurable) ?_
  filter_upwards [hSC] with z hz
  rw [norm_smul, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_right hz (norm_nonneg _)

end PairingTransfer

section PairingIdentity

variable {a b : ℝ} {χ : ℝ → ℝ} {H : ℂ → ℝ}

lemma norm_nUnit {z : ℂ} (hz : z ≠ 0) : ‖nUnit z‖ = 1 := by
  have hnz : ‖z‖ ≠ 0 := norm_ne_zero_iff.mpr hz
  rw [nUnit, norm_smul, Real.norm_eq_abs,
    abs_of_pos (inv_pos.mpr (lt_of_le_of_ne (norm_nonneg z) (Ne.symm hnz))),
    inv_mul_cancel₀ hnz]

/-- The bounded-scalar package for the two radial-identity integrands. -/
lemma scalar_bounds (ha : 0 < a) (hχ : ContDiff ℝ (⊤ : ℕ∞) χ)
    (hχc : HasCompactSupport χ) (hχs : tsupport χ ⊆ Ioo a b)
    (hH : ContDiff ℝ (⊤ : ℕ∞) H) :
    ∃ C : ℝ, (∀ᵐ z ∂(volume.restrict (annulusSet a b)),
        |(deriv (radialProfile χ) ‖z‖ + radialProfile χ ‖z‖ * ‖z‖⁻¹)
          * angExt H z| ≤ C) ∧
      (∀ᵐ z ∂(volume.restrict (annulusSet a b)),
        |radialProfile χ ‖z‖ * angExt H z| ≤ C) := by
  set φ := radialProfile χ with hφdef
  have hφsm := contDiff_radialProfile ha hχ hχs
  have hφc := hasCompactSupport_radialProfile (χ := χ) hχc
  obtain ⟨C1, hC1⟩ := hφc.deriv.exists_bound_of_continuous
    (contDiff_infty_iff_deriv.mp hφsm).2.continuous
  obtain ⟨C2, hC2⟩ := hφc.exists_bound_of_continuous hφsm.continuous
  obtain ⟨z₀, _, hz₀'⟩ := (isCompact_sphere (0 : ℂ) 1).exists_isMaxOn
    ⟨1, by simp⟩ hH.continuous.abs.continuousOn
  have hz₀ : ∀ z ∈ Metric.sphere (0 : ℂ) 1, |H z| ≤ |H z₀| := fun z hzm => hz₀' hzm
  set C3 : ℝ := |H z₀| with hC3def
  have hC3nn : 0 ≤ C3 := abs_nonneg _
  have hC1' : ∀ t : ℝ, |deriv φ t| ≤ |C1| := fun t =>
    le_trans (by simpa using hC1 t) (le_abs_self C1)
  have hC2' : ∀ t : ℝ, |φ t| ≤ |C2| := fun t =>
    le_trans (by simpa using hC2 t) (le_abs_self C2)
  have hann : ∀ z ∈ annulusSet a b, z ≠ 0 ∧ a < ‖z‖ ∧ |angExt H z| ≤ C3 := by
    intro z hz
    have hz0 : z ≠ 0 := by
      intro h0
      rw [h0] at hz
      exact absurd (mem_annulusSet.mp hz).1 (by simp [not_lt.mpr ha.le])
    refine ⟨hz0, (mem_annulusSet.mp hz).1, ?_⟩
    rw [angExt]
    exact hz₀ (nUnit z) (mem_sphere_zero_iff_norm.mpr (norm_nUnit hz0))
  refine ⟨(|C1| + |C2| * a⁻¹ + |C2|) * C3, ?_, ?_⟩
  · filter_upwards [ae_restrict_mem measurableSet_annulusSet] with z hz
    obtain ⟨hz0, hzn, hHb⟩ := hann z hz
    rw [abs_mul]
    refine mul_le_mul ?_ hHb (abs_nonneg _) (by positivity)
    refine le_trans (abs_add_le _ _) ?_
    have h2 : |φ ‖z‖ * ‖z‖⁻¹| ≤ |C2| * a⁻¹ := by
      rw [abs_mul, abs_of_pos (inv_pos.mpr (lt_trans ha hzn))]
      refine mul_le_mul (hC2' _) ?_ (by positivity) (abs_nonneg _)
      have := one_div_le_one_div_of_le ha hzn.le
      rwa [one_div, one_div] at this
    have h1 := hC1' ‖z‖
    have h3 : (0:ℝ) ≤ |C2| := abs_nonneg _
    linarith
  · filter_upwards [ae_restrict_mem measurableSet_annulusSet] with z hz
    obtain ⟨hz0, hzn, hHb⟩ := hann z hz
    rw [abs_mul]
    refine mul_le_mul ?_ hHb (abs_nonneg _) (by positivity)
    have h1 : (0:ℝ) ≤ |C1| := abs_nonneg _
    have h2 : (0:ℝ) ≤ |C2| * a⁻¹ :=
      mul_nonneg (abs_nonneg _) (inv_pos.mpr ha).le
    have := hC2' ‖z‖
    linarith

end PairingIdentity

end KsIndex.Trace
