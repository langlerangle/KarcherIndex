module

/-
KsIndexLean — Dyadic annuli and dilation estimates on the complex plane.

The closed annulus `dyadicAnnulus ρ` has radii `ρ/2` and `ρ`. Positive real
dilation scales its radius; when `ρ > 0`, the annulus excludes the origin.
For a measurable set `A` and `c > 0`, restricted nonnegative integrals scale
by `c⁻²`, and the extended `L²` norm of `v(c·)` scales by `c⁻¹` on `c • A`.
These identities use the real dimension two of the complex plane and do not
require a finite norm.

For real-valued `v` with derivative `Dv` continuous on a set containing two
adjacent annuli, the final estimate bounds the integral of
`‖v(2x) - v(x)‖²` on the inner annulus by `ρ²` times the integral of the
squared operator norm of `Dv` on the pair. The proof uses the fundamental
theorem of calculus along radial segments, Cauchy–Schwarz, and dilation.
The estimate takes values in `ℝ≥0∞`; no boundedness assumption on `v` or
finite-energy hypothesis is required.
-/
public import KsIndexLean.EndChartSheets
public import TauCeti.MeasureTheory.Integral.Dilation

@[expose] public section


noncomputable section
open Set MeasureTheory
open scoped Pointwise
open scoped ENNReal
namespace KsIndex.EndChart

variable {F : Type*} [NormedAddCommGroup F]

/-- The closed dyadic annulus with outer radius `ρ`. -/
def dyadicAnnulus (ρ : ℝ) : Set ℂ := {ζ : ℂ | ρ / 2 ≤ ‖ζ‖ ∧ ‖ζ‖ ≤ ρ}

lemma measurableSet_dyadicAnnulus (ρ : ℝ) :
    MeasurableSet (dyadicAnnulus ρ) :=
  (measurableSet_le measurable_const measurable_norm).inter
    (measurableSet_le measurable_norm measurable_const)

lemma notMem_dyadicAnnulus_zero {ρ : ℝ} (hρ : 0 < ρ) :
    (0 : ℂ) ∉ dyadicAnnulus ρ := by
  intro h
  have : ρ / 2 ≤ 0 := by simpa [dyadicAnnulus] using h.1
  linarith

/-- Real dilation carries annuli to annuli. -/
lemma smul_dyadicAnnulus {c : ℝ} (hc : 0 < c) (ρ : ℝ) :
    c • dyadicAnnulus ρ = dyadicAnnulus (c * ρ) := by
  ext ζ
  constructor
  · rintro ⟨y, ⟨hy1, hy2⟩, rfl⟩
    have hn : ‖c • y‖ = c * ‖y‖ := by
      rw [norm_smul, Real.norm_of_nonneg hc.le]
    constructor
    · rw [hn]
      calc c * ρ / 2 = c * (ρ / 2) := by ring
        _ ≤ c * ‖y‖ := by nlinarith
    · rw [hn]
      nlinarith
  · rintro ⟨h1, h2⟩
    refine ⟨c⁻¹ • ζ, ⟨?_, ?_⟩, ?_⟩
    · have hn : ‖c⁻¹ • ζ‖ = c⁻¹ * ‖ζ‖ := by
        rw [norm_smul, Real.norm_of_nonneg (by positivity)]
      rw [hn]
      calc ρ / 2 = c⁻¹ * c * (ρ / 2) := by
            rw [inv_mul_cancel₀ hc.ne', one_mul]
        _ = c⁻¹ * (c * ρ / 2) := by ring
        _ ≤ c⁻¹ * ‖ζ‖ := mul_le_mul_of_nonneg_left h1 (by positivity)
    · have hn : ‖c⁻¹ • ζ‖ = c⁻¹ * ‖ζ‖ := by
        rw [norm_smul, Real.norm_of_nonneg (by positivity)]
      rw [hn]
      calc c⁻¹ * ‖ζ‖ ≤ c⁻¹ * (c * ρ) := by
            have hcinv : (0:ℝ) < c⁻¹ := by positivity
            nlinarith
        _ = ρ := by rw [← mul_assoc, inv_mul_cancel₀ hc.ne', one_mul]
    · change c • c⁻¹ • ζ = ζ
      rw [smul_smul, mul_inv_cancel₀ hc.ne', one_smul]

/-- Adjacent annuli tile: `Aₚ ∪ A₂ₚ = {ρ/2 ≤ ‖ζ‖ ≤ 2ρ}`. -/
lemma union_dyadicAnnulus (ρ : ℝ) :
    dyadicAnnulus ρ ∪ dyadicAnnulus (2 * ρ)
      = {ζ : ℂ | ρ / 2 ≤ ‖ζ‖ ∧ ‖ζ‖ ≤ 2 * ρ} := by
  ext ζ
  simp only [dyadicAnnulus, mem_union, Set.mem_ofPred_eq]
  constructor
  · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
    · exact ⟨h1, by linarith⟩
    · exact ⟨by linarith, h2⟩
  · rintro ⟨h1, h2⟩
    rcases le_or_gt ‖ζ‖ ρ with h | h
    · exact Or.inl ⟨h1, h⟩
    · exact Or.inr ⟨by linarith, h2⟩

/-- **Restricted nonnegative-integral dilation**: for `c > 0`,
`∫⁻_A g(c·x) dx = c⁻² ∫⁻_{c·A} g` — TauCeti's whole-space dilation law
carried through the indicator; `n = dim_ℝ ℂ = 2`. -/
lemma setLIntegral_comp_smul (g : ℂ → ℝ≥0∞) {c : ℝ} (hc : 0 < c)
    {A : Set ℂ} (hA : MeasurableSet A) :
    (∫⁻ x in A, g (c • x) ∂volume)
      = ENNReal.ofReal (c ^ 2)⁻¹ * ∫⁻ y in c • A, g y ∂volume := by
  have hcA : MeasurableSet (c • A) := hA.const_smul₀ c
  have hind : A.indicator (fun x => g (c • x))
      = fun x => (c • A).indicator g (c • x) := by
    funext x
    by_cases hx : x ∈ A
    · rw [Set.indicator_of_mem hx, Set.indicator_of_mem (smul_mem_smul_set hx)]
    · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem
        (fun hmem => hx ((smul_mem_smul_set_iff₀ hc.ne' A x).mp hmem))]
  rw [← lintegral_indicator hA, hind,
    TauCeti.lintegral_comp_smul volume ((c • A).indicator g) hc.ne',
    lintegral_indicator hcA]
  congr 2
  rw [Complex.finrank_real_complex, abs_of_nonneg (by positivity)]

/-- **Restricted `L²` dilation**: `‖v(c·)‖_{L²(A)} = c⁻¹·‖v‖_{L²(c·A)}`
— the 2D scaling exponent `n/p = 2/2 = 1`. -/
lemma eLpNorm_comp_smul_restrict (v : ℂ → F) {c : ℝ} (hc : 0 < c)
    {A : Set ℂ} (hA : MeasurableSet A) :
    eLpNorm (fun x => v (c • x)) 2 (volume.restrict A)
      = ENNReal.ofReal c⁻¹ * eLpNorm v 2 (volume.restrict (c • A)) := by
  have he : MeasurableEmbedding (fun x : ℂ => c • x) :=
    (Homeomorph.smul (isUnit_iff_ne_zero.mpr hc.ne').unit).toMeasurableEquiv.measurableEmbedding
  have hpre : (fun x : ℂ => c • x) ⁻¹' (c • A) = A := by
    ext x
    exact smul_mem_smul_set_iff₀ hc.ne' A x
  have hmap : Measure.map (fun x : ℂ => c • x) (volume.restrict A) =
      ENNReal.ofReal (c ^ 2)⁻¹ • volume.restrict (c • A) := by
    nth_rw 1 [← hpre]
    rw [← he.restrict_map, Measure.map_addHaar_smul volume hc.ne',
      Measure.restrict_smul, Complex.finrank_real_complex,
      abs_of_nonneg (by positivity)]
  change eLpNorm (v ∘ (fun x : ℂ => c • x)) 2 (volume.restrict A) = _
  rw [← he.eLpNorm_map_measure, hmap,
    eLpNorm_smul_measure_of_ne_zero_of_ne_top (by norm_num) (by norm_num)]
  norm_num only [ENNReal.toReal_div, ENNReal.toReal_one, ENNReal.toReal_ofNat, smul_eq_mul]
  congr 1
  rw [ENNReal.ofReal_rpow_of_pos (by positivity)]
  congr 1
  rw [← Real.rpow_natCast c 2, ← Real.rpow_neg hc.le, ← Real.rpow_mul hc.le]
  have hexp : (-((2:ℕ):ℝ)) * (1/2) = -1 := by norm_num
  rw [hexp, Real.rpow_neg_one]

/-! ### The radial doubling estimate

Compare `v` with its doubling `v(2·)` on an annulus: the difference along
the radial segment `[x, 2x]` is an integral of the derivative, the segment
stays inside the adjacent-annulus pair, Cauchy–Schwarz in the segment
parameter and the per-slice dilation identity land the square of the
difference under `ρ²` times the pair energy.  No boundedness of `v` is
assumed. -/

/-- The radial segment `[x, 2x]` over an annulus point stays in the
adjacent-annulus pair. -/
lemma segment_mem_pair {ρ : ℝ} (hρ : 0 < ρ) {x : ℂ}
    (hx : x ∈ dyadicAnnulus ρ) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    x + t • x ∈ dyadicAnnulus ρ ∪ dyadicAnnulus (2 * ρ) := by
  obtain ⟨hx1, hx2⟩ := hx
  obtain ⟨ht0, ht1⟩ := ht
  have hxn : (0:ℝ) ≤ ‖x‖ := norm_nonneg x
  have hseg : x + t • x = (1 + t) • x := by
    rw [add_smul, one_smul]
  have hn : ‖x + t • x‖ = (1 + t) * ‖x‖ := by
    rw [hseg, norm_smul, Real.norm_of_nonneg (by linarith)]
  rw [union_dyadicAnnulus, Set.mem_ofPred_eq, hn]
  constructor
  · nlinarith
  · nlinarith

/-- The dilated annulus stays in the adjacent-annulus pair, for dilation
factors in `[1, 2]`. -/
lemma smul_dyadicAnnulus_subset_pair {ρ : ℝ} (hρ : 0 < ρ) {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) 1) :
    (1 + t) • dyadicAnnulus ρ
      ⊆ dyadicAnnulus ρ ∪ dyadicAnnulus (2 * ρ) := by
  obtain ⟨ht0, ht1⟩ := ht
  rw [smul_dyadicAnnulus (by linarith : (0:ℝ) < 1 + t), union_dyadicAnnulus]
  rintro ζ ⟨h1, h2⟩
  constructor
  · nlinarith [norm_nonneg ζ]
  · nlinarith [norm_nonneg ζ]

/-- Operator bound in `ℝ≥0∞`: `‖L x‖ₑ ≤ ‖L‖ₑ · ‖x‖ₑ`. -/
lemma enorm_apply_le_enorm_mul (L : ℂ →L[ℝ] ℝ) (x : ℂ) :
    ‖L x‖ₑ ≤ ‖L‖ₑ * ‖x‖ₑ := by
  rw [← ofReal_norm, ← ofReal_norm, ← ofReal_norm,
    ← ENNReal.ofReal_mul (norm_nonneg L)]
  exact ENNReal.ofReal_le_ofReal (L.le_opNorm x)

/-- **Pointwise radial doubling bound**: for `x` in the annulus,
`‖v(2x) − v(x)‖ₑ² ≤ ‖x‖ₑ² · ∫_0^1 ‖Dv((1+t)x)‖ₑ² dt` — fundamental theorem
along the radial segment, operator bound, and Cauchy–Schwarz in `t`. -/
lemma enorm_sq_sub_doubling_le {U : Set ℂ} (v : ℂ → ℝ)
    (Dv : ℂ → (ℂ →L[ℝ] ℝ)) (hv : ∀ ζ ∈ U, HasFDerivAt v (Dv ζ) ζ)
    (hDvc : ContinuousOn Dv U) {ρ : ℝ} (hρ : 0 < ρ)
    (hsub : dyadicAnnulus ρ ∪ dyadicAnnulus (2 * ρ) ⊆ U)
    {x : ℂ} (hx : x ∈ dyadicAnnulus ρ) :
    ‖v ((2:ℝ) • x) - v x‖ₑ ^ 2
      ≤ ‖x‖ₑ ^ 2 * ∫⁻ t in Icc (0:ℝ) 1, ‖Dv (x + t • x)‖ₑ ^ 2 ∂volume := by
  have hsegc : Continuous (fun t : ℝ => x + t • x) :=
    continuous_const.add (continuous_id.smul continuous_const)
  have hmaps : MapsTo (fun t : ℝ => x + t • x) (Icc (0:ℝ) 1) U :=
    fun t ht => hsub (segment_mem_pair hρ hx ht)
  -- the derivative of the segment composite
  have hchain : ∀ t ∈ Icc (0:ℝ) 1,
      HasDerivAt (fun s : ℝ => v (x + s • x)) ((Dv (x + t • x)) x) t := by
    intro t ht
    have hγ : HasDerivAt (fun s : ℝ => x + s • x) x t := by
      simpa using ((hasDerivAt_id t).smul_const x).const_add x
    exact (hv _ (hmaps ht)).comp_hasDerivAt t hγ
  -- continuity of the integrand on the segment
  have hDvt : ContinuousOn (fun t : ℝ => Dv (x + t • x)) (Icc (0:ℝ) 1) :=
    hDvc.comp hsegc.continuousOn hmaps
  have hcont : ContinuousOn (fun t : ℝ => (Dv (x + t • x)) x) (Icc (0:ℝ) 1) :=
    hDvt.clm_apply continuousOn_const
  -- FTC along the segment
  have hFTC : v ((2:ℝ) • x) - v x
      = ∫ t in (0:ℝ)..1, (Dv (x + t • x)) x := by
    have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
      (f := fun s : ℝ => v (x + s • x))
      (f' := fun t : ℝ => (Dv (x + t • x)) x)
      (fun t ht => hchain t (by rwa [Set.uIcc_of_le zero_le_one] at ht))
      (hcont.intervalIntegrable_of_Icc zero_le_one)
    rw [h]
    congr 1 <;> simp [two_smul]
  -- enorm of the interval integral
  have hstep1 : ‖v ((2:ℝ) • x) - v x‖ₑ
      ≤ (∫⁻ t in Icc (0:ℝ) 1, ‖Dv (x + t • x)‖ₑ ∂volume) * ‖x‖ₑ := by
    rw [hFTC, intervalIntegral.integral_of_le zero_le_one]
    calc ‖∫ t in Ioc (0:ℝ) 1, (Dv (x + t • x)) x ∂volume‖ₑ
        ≤ ∫⁻ t in Ioc (0:ℝ) 1, ‖(Dv (x + t • x)) x‖ₑ ∂volume :=
          enorm_integral_le_lintegral_enorm _
      _ ≤ ∫⁻ t in Icc (0:ℝ) 1, ‖(Dv (x + t • x)) x‖ₑ ∂volume :=
          lintegral_mono_set Ioc_subset_Icc_self
      _ ≤ ∫⁻ t in Icc (0:ℝ) 1, ‖Dv (x + t • x)‖ₑ * ‖x‖ₑ ∂volume :=
          lintegral_mono fun t => enorm_apply_le_enorm_mul _ x
      _ = (∫⁻ t in Icc (0:ℝ) 1, ‖Dv (x + t • x)‖ₑ ∂volume) * ‖x‖ₑ :=
          lintegral_mul_const' _ _ enorm_ne_top
  -- Cauchy–Schwarz in t on the unit interval
  have hCS : (∫⁻ t in Icc (0:ℝ) 1, ‖Dv (x + t • x)‖ₑ ∂volume) ^ 2
      ≤ ∫⁻ t in Icc (0:ℝ) 1, ‖Dv (x + t • x)‖ₑ ^ 2 ∂volume := by
    have hmeas : AEMeasurable (fun t : ℝ => ‖Dv (x + t • x)‖ₑ)
        (volume.restrict (Icc (0:ℝ) 1)) :=
      (hDvt.aemeasurable measurableSet_Icc).enorm
    have hH := ENNReal.lintegral_mul_le_Lp_mul_Lq
      (volume.restrict (Icc (0:ℝ) 1))
      Real.HolderConjugate.two_two
      hmeas aemeasurable_const (g := fun _ => (1 : ℝ≥0∞))
    simp only [Pi.mul_apply, mul_one, ENNReal.one_rpow, lintegral_const,
      MeasureTheory.Measure.restrict_apply MeasurableSet.univ,
      Set.univ_inter, Real.volume_Icc, sub_zero, ENNReal.ofReal_one] at hH
    calc (∫⁻ t in Icc (0:ℝ) 1, ‖Dv (x + t • x)‖ₑ ∂volume) ^ 2
        ≤ ((∫⁻ t in Icc (0:ℝ) 1,
              ‖Dv (x + t • x)‖ₑ ^ (2:ℝ) ∂volume) ^ (1/2 : ℝ)) ^ 2 := by
          gcongr
      _ = ∫⁻ t in Icc (0:ℝ) 1, ‖Dv (x + t • x)‖ₑ ^ 2 ∂volume := by
          rw [← ENNReal.rpow_natCast
            ((∫⁻ t in Icc (0:ℝ) 1, ‖Dv (x + t • x)‖ₑ ^ (2:ℝ) ∂volume)
              ^ (1/2 : ℝ)) 2, ← ENNReal.rpow_mul]
          norm_num
  calc ‖v ((2:ℝ) • x) - v x‖ₑ ^ 2
      ≤ ((∫⁻ t in Icc (0:ℝ) 1, ‖Dv (x + t • x)‖ₑ ∂volume) * ‖x‖ₑ) ^ 2 := by
        gcongr
    _ = (∫⁻ t in Icc (0:ℝ) 1, ‖Dv (x + t • x)‖ₑ ∂volume) ^ 2 * ‖x‖ₑ ^ 2 :=
        mul_pow _ _ 2
    _ ≤ (∫⁻ t in Icc (0:ℝ) 1, ‖Dv (x + t • x)‖ₑ ^ 2 ∂volume) * ‖x‖ₑ ^ 2 := by
        gcongr
    _ = ‖x‖ₑ ^ 2 * ∫⁻ t in Icc (0:ℝ) 1, ‖Dv (x + t • x)‖ₑ ^ 2 ∂volume :=
        mul_comm _ _

/-- **The annulus doubling estimate**: the square of the doubling
difference integrates to at most `ρ²` times the pair energy —
`∫_{Aₚ} ‖v(2x) − v(x)‖ₑ² ≤ ρ² · ∫_{Aₚ ∪ A₂ₚ} ‖Dv‖ₑ²`. -/
theorem lintegral_sq_sub_doubling_le {U : Set ℂ} (v : ℂ → ℝ)
    (Dv : ℂ → (ℂ →L[ℝ] ℝ)) (hv : ∀ ζ ∈ U, HasFDerivAt v (Dv ζ) ζ)
    (hDvc : ContinuousOn Dv U) {ρ : ℝ} (hρ : 0 < ρ)
    (hsub : dyadicAnnulus ρ ∪ dyadicAnnulus (2 * ρ) ⊆ U) :
    (∫⁻ x in dyadicAnnulus ρ, ‖v ((2:ℝ) • x) - v x‖ₑ ^ 2 ∂volume)
      ≤ ENNReal.ofReal (ρ ^ 2)
          * ∫⁻ ζ in dyadicAnnulus ρ ∪ dyadicAnnulus (2 * ρ),
              ‖Dv ζ‖ₑ ^ 2 ∂volume := by
  set A : Set ℂ := dyadicAnnulus ρ with hAdef
  have hA : MeasurableSet A := measurableSet_dyadicAnnulus ρ
  set Epair : ℝ≥0∞ :=
    ∫⁻ ζ in dyadicAnnulus ρ ∪ dyadicAnnulus (2 * ρ), ‖Dv ζ‖ₑ ^ 2 ∂volume
    with hEdef
  -- pointwise bound then Tonelli
  have hstep : (∫⁻ x in A, ‖v ((2:ℝ) • x) - v x‖ₑ ^ 2 ∂volume)
      ≤ ENNReal.ofReal (ρ ^ 2) * ∫⁻ x in A,
          ∫⁻ t in Icc (0:ℝ) 1, ‖Dv (x + t • x)‖ₑ ^ 2 ∂volume ∂volume := by
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    apply lintegral_mono_ae
    filter_upwards [ae_restrict_mem hA] with x hxA
    calc ‖v ((2:ℝ) • x) - v x‖ₑ ^ 2
        ≤ ‖x‖ₑ ^ 2 * ∫⁻ t in Icc (0:ℝ) 1, ‖Dv (x + t • x)‖ₑ ^ 2 ∂volume :=
          enorm_sq_sub_doubling_le v Dv hv hDvc hρ hsub hxA
      _ ≤ ENNReal.ofReal (ρ ^ 2)
            * ∫⁻ t in Icc (0:ℝ) 1, ‖Dv (x + t • x)‖ₑ ^ 2 ∂volume := by
          gcongr
          rw [← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg x)]
          exact ENNReal.ofReal_le_ofReal
            (by nlinarith [hxA.1, hxA.2, norm_nonneg x])
  refine hstep.trans ?_
  gcongr
  -- Tonelli swap, then the per-slice dilation bound
  have hmeasp : AEMeasurable
      (fun p : ℂ × ℝ => ‖Dv (p.1 + p.2 • p.1)‖ₑ ^ 2)
      ((volume.restrict A).prod (volume.restrict (Icc (0:ℝ) 1))) := by
    rw [Measure.prod_restrict]
    have hsegc : Continuous (fun p : ℂ × ℝ => p.1 + p.2 • p.1) :=
      continuous_fst.add (continuous_snd.smul continuous_fst)
    have hmapsp : MapsTo (fun p : ℂ × ℝ => p.1 + p.2 • p.1)
        (A ×ˢ Icc (0:ℝ) 1) U := by
      rintro ⟨x, t⟩ ⟨hxA, ht⟩
      exact hsub (segment_mem_pair hρ hxA ht)
    exact (((hDvc.comp hsegc.continuousOn hmapsp).aemeasurable
      (hA.prod measurableSet_Icc)).enorm).pow_const 2
  calc (∫⁻ x in A, ∫⁻ t in Icc (0:ℝ) 1,
          ‖Dv (x + t • x)‖ₑ ^ 2 ∂volume ∂volume)
      = ∫⁻ t in Icc (0:ℝ) 1, ∫⁻ x in A,
          ‖Dv (x + t • x)‖ₑ ^ 2 ∂volume ∂volume :=
        lintegral_lintegral_swap hmeasp
    _ ≤ ∫⁻ _ in Icc (0:ℝ) 1, Epair ∂volume := by
        apply lintegral_mono_ae
        filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
        have ht1 : (0:ℝ) < 1 + t := by
          have := ht.1; linarith
        calc (∫⁻ x in A, ‖Dv (x + t • x)‖ₑ ^ 2 ∂volume)
            = ∫⁻ x in A, ‖Dv ((1 + t) • x)‖ₑ ^ 2 ∂volume :=
              lintegral_congr fun x => by rw [add_smul, one_smul]
          _ = ENNReal.ofReal ((1 + t) ^ 2)⁻¹
                * ∫⁻ y in (1 + t) • A, ‖Dv y‖ₑ ^ 2 ∂volume :=
              setLIntegral_comp_smul (fun y => ‖Dv y‖ₑ ^ 2) ht1 hA
          _ ≤ 1 * ∫⁻ y in dyadicAnnulus ρ ∪ dyadicAnnulus (2 * ρ),
                ‖Dv y‖ₑ ^ 2 ∂volume := by
              gcongr
              · exact ENNReal.ofReal_le_one.mpr (by
                  rw [inv_le_one_iff₀]
                  right
                  nlinarith [ht.1])
              · exact smul_dyadicAnnulus_subset_pair hρ ht
          _ = Epair := by rw [one_mul]
    _ = Epair := by
        rw [setLIntegral_const, Real.volume_Icc, sub_zero,
          ENNReal.ofReal_one, mul_one]

end KsIndex.EndChart
