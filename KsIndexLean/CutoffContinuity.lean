module

/-
Pointwise and integrated estimates for the disk pairing of a cutoff pair.

For a real-valued cutoff `c` (values in `[0,1]`) and `f, g : ℂ → ℂ`, with `χ = ↑c` the
complex-valued cutoff, the product rule gives at every point of differentiability
    `gradInner (χf) (χg) − gradInner f g = (c² − 1)·gradInner f g
       + c·Σ_v (∂_v c)(conj(∂_v f)·g + conj f·∂_v g) + Σ_v (∂_v c)²·conj f·g`
(`gradInner_cutoff_sub`, `v ∈ {1, I}`), hence the **pointwise bound** `gradInner_cutoff_bound`:
    `‖gradInner (χf) (χg) − gradInner f g‖
       ≤ (1 − c²)·‖gradInner f g‖ + (Df·Mg + Mf·Dg)·(|∂₁c| + |∂_I c|) + Mf·Mg·(|∂₁c|² + |∂_I c|²)`
for `‖f‖ ≤ Mf`, `‖∇f‖ ≤ Df` (and likewise `g`) at the point.

The integrated estimate `Bd_cutoff_bound` is proved in this module for the puncture
cutoff, k ≥ 2, 0 < ε < 1, and an auxiliary δ > 0. It assumes differentiability and
uniform value and derivative bounds on the disk, and controls the pairing error
by puncture-neighborhood area, a term proportional to δ, and cutoff energy with
a coefficient involving 1/δ. Together with vanishing area and cutoff energy,
choosing δ appropriately yields pairing convergence; the final theorem here
is the quantitative bound.
-/
public import KsIndexLean.PunctureCutoffP
public import KsIndexLean.ModeDiag

@[expose] public section


noncomputable section

open Complex MeasureTheory Filter

namespace KsIndex.CutoffContinuity

open KsIndex.Surface KsIndex.SurfaceForm KsIndex.GradOrtho KsIndex.PunctureCutoff KsIndex.ModeDiag

variable {k : ℕ}

/-- The complex-valued cutoff times `f`. -/
def cutMul (c : ℂ → ℝ) (f : ℂ → ℂ) (w : ℂ) : ℂ := (c w : ℂ) * f w

lemma hasFDerivAt_cutMul {c : ℂ → ℝ} {f : ℂ → ℂ} {w : ℂ} (hc : DifferentiableAt ℝ c w)
    (hf : DifferentiableAt ℝ f w) :
    HasFDerivAt (cutMul c f)
      ((c w : ℂ) • fderiv ℝ f w + f w • (Complex.ofRealCLM.comp (fderiv ℝ c w))) w := by
  have hcC : HasFDerivAt (fun z => (c z : ℂ)) (Complex.ofRealCLM.comp (fderiv ℝ c w)) w :=
    Complex.ofRealCLM.hasFDerivAt.comp w hc.hasFDerivAt
  exact hcC.mul hf.hasFDerivAt

lemma fderiv_cutMul_apply {c : ℂ → ℝ} {f : ℂ → ℂ} {w : ℂ} (hc : DifferentiableAt ℝ c w)
    (hf : DifferentiableAt ℝ f w) (v : ℂ) :
    fderiv ℝ (cutMul c f) w v = (c w : ℂ) * fderiv ℝ f w v + (fderiv ℝ c w v : ℂ) * f w := by
  rw [(hasFDerivAt_cutMul hc hf).fderiv]
  simp [smul_eq_mul, mul_comm]

/-- **The exact expansion** of the gradient cross density of a cut-off pair. -/
lemma gradInner_cutoff_sub {c : ℂ → ℝ} {f g : ℂ → ℂ} {w : ℂ} (hc : DifferentiableAt ℝ c w)
    (hf : DifferentiableAt ℝ f w) (hg : DifferentiableAt ℝ g w) :
    gradInner (cutMul c f) (cutMul c g) w - gradInner f g w
      = ((c w ^ 2 - 1 : ℝ) : ℂ) * gradInner f g w
        + (c w : ℂ) * ((fderiv ℝ c w 1 : ℂ)
            * ((starRingEnd ℂ) (fderiv ℝ f w 1) * g w + (starRingEnd ℂ) (f w) * fderiv ℝ g w 1)
          + (fderiv ℝ c w I : ℂ)
            * ((starRingEnd ℂ) (fderiv ℝ f w I) * g w + (starRingEnd ℂ) (f w) * fderiv ℝ g w I))
        + (((fderiv ℝ c w 1) ^ 2 + (fderiv ℝ c w I) ^ 2 : ℝ) : ℂ)
            * ((starRingEnd ℂ) (f w) * g w) := by
  simp only [gradInner, fderiv_cutMul_apply hc hf, fderiv_cutMul_apply hc hg, map_add, map_mul,
    Complex.conj_ofReal]
  push_cast
  ring

/-- **The pointwise bound.** -/
lemma gradInner_cutoff_bound {c : ℂ → ℝ} {f g : ℂ → ℂ} {w : ℂ} (hc : DifferentiableAt ℝ c w)
    (hf : DifferentiableAt ℝ f w) (hg : DifferentiableAt ℝ g w)
    (hc0 : 0 ≤ c w) (hc1 : c w ≤ 1) {Mf Df Mg Dg : ℝ}
    (hMf : ‖f w‖ ≤ Mf) (hDf : ‖fderiv ℝ f w‖ ≤ Df)
    (hMg : ‖g w‖ ≤ Mg) (hDg : ‖fderiv ℝ g w‖ ≤ Dg) :
    ‖gradInner (cutMul c f) (cutMul c g) w - gradInner f g w‖
      ≤ (1 - c w ^ 2) * ‖gradInner f g w‖
        + (Df * Mg + Mf * Dg) * (|fderiv ℝ c w 1| + |fderiv ℝ c w I|)
        + Mf * Mg * ((fderiv ℝ c w 1) ^ 2 + (fderiv ℝ c w I) ^ 2) := by
  rw [gradInner_cutoff_sub hc hf hg]
  have hMf0 : 0 ≤ Mf := le_trans (norm_nonneg _) hMf
  have hMg0 : 0 ≤ Mg := le_trans (norm_nonneg _) hMg
  have hDf0 : 0 ≤ Df := le_trans (norm_nonneg _) hDf
  have hDg0 : 0 ≤ Dg := le_trans (norm_nonneg _) hDg
  have hf1 : ‖fderiv ℝ f w 1‖ ≤ Df := le_trans (by simpa using (fderiv ℝ f w).le_opNorm 1) hDf
  have hfI : ‖fderiv ℝ f w I‖ ≤ Df := le_trans (by simpa using (fderiv ℝ f w).le_opNorm I) hDf
  have hg1 : ‖fderiv ℝ g w 1‖ ≤ Dg := le_trans (by simpa using (fderiv ℝ g w).le_opNorm 1) hDg
  have hgI : ‖fderiv ℝ g w I‖ ≤ Dg := le_trans (by simpa using (fderiv ℝ g w).le_opNorm I) hDg
  set a1 := fderiv ℝ c w 1; set aI := fderiv ℝ c w I
  -- each of the three groups
  have T1 : ‖((c w ^ 2 - 1 : ℝ) : ℂ) * gradInner f g w‖ = (1 - c w ^ 2) * ‖gradInner f g w‖ := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonpos (by nlinarith)]; ring
  have Tcross : ∀ (av : ℝ) (df dg : ℂ), ‖df‖ ≤ Df → ‖dg‖ ≤ Dg →
      ‖(av : ℂ) * ((starRingEnd ℂ) df * g w + (starRingEnd ℂ) (f w) * dg)‖
        ≤ |av| * (Df * Mg + Mf * Dg) := by
    intro av df dg hdf hdg
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    gcongr
    calc ‖(starRingEnd ℂ) df * g w + (starRingEnd ℂ) (f w) * dg‖
        ≤ ‖(starRingEnd ℂ) df * g w‖ + ‖(starRingEnd ℂ) (f w) * dg‖ := norm_add_le _ _
      _ = ‖df‖ * ‖g w‖ + ‖f w‖ * ‖dg‖ := by
          rw [norm_mul, norm_mul, Complex.norm_conj, Complex.norm_conj]
      _ ≤ Df * Mg + Mf * Dg := by gcongr
  have T2 : ‖(c w : ℂ) * ((a1 : ℂ) * ((starRingEnd ℂ) (fderiv ℝ f w 1) * g w
        + (starRingEnd ℂ) (f w) * fderiv ℝ g w 1)
      + (aI : ℂ) * ((starRingEnd ℂ) (fderiv ℝ f w I) * g w
        + (starRingEnd ℂ) (f w) * fderiv ℝ g w I))‖
      ≤ (Df * Mg + Mf * Dg) * (|a1| + |aI|) := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hc0]
    calc c w * ‖_‖ ≤ 1 * ‖(a1 : ℂ) * ((starRingEnd ℂ) (fderiv ℝ f w 1) * g w
          + (starRingEnd ℂ) (f w) * fderiv ℝ g w 1)
        + (aI : ℂ) * ((starRingEnd ℂ) (fderiv ℝ f w I) * g w
          + (starRingEnd ℂ) (f w) * fderiv ℝ g w I)‖ := by gcongr
      _ ≤ 1 * (|a1| * (Df * Mg + Mf * Dg) + |aI| * (Df * Mg + Mf * Dg)) := by
          gcongr
          exact le_trans (norm_add_le _ _) (add_le_add (Tcross a1 _ _ hf1 hg1)
            (Tcross aI _ _ hfI hgI))
      _ = (Df * Mg + Mf * Dg) * (|a1| + |aI|) := by ring
  have T3 : ‖((a1 ^ 2 + aI ^ 2 : ℝ) : ℂ) * ((starRingEnd ℂ) (f w) * g w)‖
      ≤ Mf * Mg * (a1 ^ 2 + aI ^ 2) := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity), norm_mul,
      Complex.norm_conj]
    calc (a1 ^ 2 + aI ^ 2) * (‖f w‖ * ‖g w‖) ≤ (a1 ^ 2 + aI ^ 2) * (Mf * Mg) := by gcongr
      _ = _ := by ring
  calc _ ≤ ‖((c w ^ 2 - 1 : ℝ) : ℂ) * gradInner f g w‖
        + ‖(c w : ℂ) * ((a1 : ℂ) * ((starRingEnd ℂ) (fderiv ℝ f w 1) * g w
            + (starRingEnd ℂ) (f w) * fderiv ℝ g w 1)
          + (aI : ℂ) * ((starRingEnd ℂ) (fderiv ℝ f w I) * g w
            + (starRingEnd ℂ) (f w) * fderiv ℝ g w I))‖
        + ‖((a1 ^ 2 + aI ^ 2 : ℝ) : ℂ) * ((starRingEnd ℂ) (f w) * g w)‖ := norm_add₃_le
    _ ≤ _ := by rw [T1]; gcongr

/-- **The potential cross density of a cut-off pair**, exactly. -/
lemma potCross_cutoff_sub (c : ℂ → ℝ) (f g : ℂ → ℂ) (V : ℝ) (w : ℂ) :
    (V : ℂ) * (starRingEnd ℂ) (cutMul c f w) * cutMul c g w
      - (V : ℂ) * (starRingEnd ℂ) (f w) * g w
      = ((c w ^ 2 - 1 : ℝ) : ℂ) * ((V : ℂ) * (starRingEnd ℂ) (f w) * g w) := by
  simp only [cutMul, map_mul, Complex.conj_ofReal]
  push_cast
  ring

lemma potCross_cutoff_bound (c : ℂ → ℝ) (f g : ℂ → ℂ) (V : ℝ) (w : ℂ)
    (hc0 : 0 ≤ c w) (hc1 : c w ≤ 1) {Mf Mg : ℝ} (hMf : ‖f w‖ ≤ Mf) (hMg : ‖g w‖ ≤ Mg) :
    ‖(V : ℂ) * (starRingEnd ℂ) (cutMul c f w) * cutMul c g w
      - (V : ℂ) * (starRingEnd ℂ) (f w) * g w‖
      ≤ (1 - c w ^ 2) * (|V| * (Mf * Mg)) := by
  rw [potCross_cutoff_sub, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonpos (by nlinarith), neg_sub, norm_mul, norm_mul, Complex.norm_real,
    Real.norm_eq_abs, Complex.norm_conj]
  have hMf0 : 0 ≤ Mf := le_trans (norm_nonneg _) hMf
  have h1 : 0 ≤ 1 - c w ^ 2 := by nlinarith
  apply mul_le_mul_of_nonneg_left _ h1
  rw [mul_assoc]
  gcongr

/-! ### The integrated half: `Bd`-continuity on the disk -/

lemma potV_nonneg (k : ℕ) (w : ℂ) : 0 ≤ potV k w := by unfold potV; positivity

lemma potV_le (_hk : 2 ≤ k) {w : ℂ} (hw : ‖w‖ ≤ 1) : potV k w ≤ 8 * ((k : ℝ) - 1) ^ 2 := by
  unfold potV
  have h1 : ‖w‖ ^ (2 * k - 4) ≤ 1 := pow_le_one₀ (norm_nonneg _) hw
  have h2 : (1 : ℝ) ≤ (‖w‖ ^ (2 * k - 2) + 1) ^ 2 := by
    nlinarith [pow_nonneg (norm_nonneg w) (2 * k - 2)]
  rw [div_le_iff₀ (by positivity)]
  calc 8 * ((k : ℝ) - 1) ^ 2 * ‖w‖ ^ (2 * k - 4) ≤ 8 * ((k : ℝ) - 1) ^ 2 * 1 := by
        gcongr
    _ ≤ 8 * ((k : ℝ) - 1) ^ 2 * (‖w‖ ^ (2 * k - 2) + 1) ^ 2 := by gcongr

lemma continuousOn_of_diff {f : ℂ → ℂ} (hf : ∀ w ∈ disk, DifferentiableAt ℝ f w) :
    ContinuousOn f disk := fun w hw => (hf w hw).continuousAt.continuousWithinAt

lemma continuous_potV (k : ℕ) : Continuous (potV k) := by
  have : potV k = fun w => KsIndex.Radial.Vrad k ‖w‖ := funext fun w => rfl
  rw [this]; exact (KsIndex.Radial.continuous_Vrad k).comp continuous_norm

/-- Integrability on the disk of a function bounded there and a.e.-strongly measurable. -/
lemma integrableOn_disk_of_bounded {f : ℂ → ℂ} {M : ℝ}
    (hm : AEStronglyMeasurable f (volume.restrict disk)) (hb : ∀ w ∈ disk, ‖f w‖ ≤ M) :
    IntegrableOn f disk := by
  have hc : IntegrableOn (fun _ : ℂ => M) disk :=
    integrableOn_const (C := M) (measure_ball_lt_top).ne
  refine Integrable.mono' hc.integrable hm ?_
  rw [ae_restrict_iff' measurableSet_disk]
  exact Eventually.of_forall hb

/-- The potential cross density is a.e.-strongly measurable on the disk. -/
lemma aesm_pot (k : ℕ) {f g : ℂ → ℂ} (hf : ContinuousOn f disk) (hg : ContinuousOn g disk) :
    AEStronglyMeasurable (fun w => (potV k w : ℂ) * (starRingEnd ℂ) (f w) * g w)
      (volume.restrict disk) := by
  have h1 : AEStronglyMeasurable (fun w => (potV k w : ℂ)) (volume.restrict disk) :=
    (Complex.continuous_ofReal.comp (continuous_potV k)).aestronglyMeasurable
  have h2 : AEStronglyMeasurable (fun w => (starRingEnd ℂ) (f w)) (volume.restrict disk) :=
    Complex.continuous_conj.comp_aestronglyMeasurable
      (hf.aestronglyMeasurable measurableSet_disk)
  exact (h1.mul h2).mul (hg.aestronglyMeasurable measurableSet_disk)

lemma integrableOn_pot (hk : 2 ≤ k) {f g : ℂ → ℂ} (hf : ContinuousOn f disk)
    (hg : ContinuousOn g disk) {Mf Mg : ℝ} (hMf : ∀ w ∈ disk, ‖f w‖ ≤ Mf)
    (hMg : ∀ w ∈ disk, ‖g w‖ ≤ Mg) :
    IntegrableOn (fun w => (potV k w : ℂ) * (starRingEnd ℂ) (f w) * g w) disk := by
  refine integrableOn_disk_of_bounded (aesm_pot k hf hg)
    (M := 8 * ((k : ℝ) - 1) ^ 2 * (Mf * Mg)) fun w hw => ?_
  rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (potV_nonneg k w),
    Complex.norm_conj]
  have hMf0 : 0 ≤ Mf := le_trans (norm_nonneg _) (hMf w hw)
  have hMg0 : 0 ≤ Mg := le_trans (norm_nonneg _) (hMg w hw)
  calc potV k w * ‖f w‖ * ‖g w‖ ≤ 8 * ((k : ℝ) - 1) ^ 2 * Mf * Mg := by
        gcongr
        · exact potV_le hk (le_of_lt (mem_disk_iff.mp hw))
        · exact hMf w hw
        · exact hMg w hw
    _ = _ := by ring

/-- `‖gradInner f g w‖ ≤ 2 ‖df‖ ‖dg‖`. -/
lemma norm_gradInner_le_of_bounded {f g : ℂ → ℂ} {w : ℂ} {Df Dg : ℝ}
    (hDf : ‖fderiv ℝ f w‖ ≤ Df) (hDg : ‖fderiv ℝ g w‖ ≤ Dg) :
    ‖gradInner f g w‖ ≤ 2 * (Df * Dg) := by
  have hDf0 : 0 ≤ Df := le_trans (norm_nonneg _) hDf
  have h1 : ∀ v : ℂ, ‖v‖ = 1 →
      ‖(starRingEnd ℂ) (fderiv ℝ f w v) * fderiv ℝ g w v‖ ≤ Df * Dg := by
    intro v hv
    rw [norm_mul, Complex.norm_conj]
    have t1 := (fderiv ℝ f w).le_opNorm v
    have t2 := (fderiv ℝ g w).le_opNorm v
    rw [hv, mul_one] at t1 t2
    exact mul_le_mul (by linarith) (by linarith) (norm_nonneg _) hDf0
  unfold gradInner
  calc _ ≤ ‖(starRingEnd ℂ) (fderiv ℝ f w 1) * fderiv ℝ g w 1‖
        + ‖(starRingEnd ℂ) (fderiv ℝ f w I) * fderiv ℝ g w I‖ := norm_add_le _ _
    _ ≤ Df * Dg + Df * Dg := add_le_add (h1 1 (by simp)) (h1 I (by simp))
    _ = _ := by ring

lemma integrableOn_gradInner_bounded {f g : ℂ → ℂ} {Df Dg : ℝ}
    (hDf : ∀ w ∈ disk, ‖fderiv ℝ f w‖ ≤ Df) (hDg : ∀ w ∈ disk, ‖fderiv ℝ g w‖ ≤ Dg) :
    IntegrableOn (gradInner f g) disk :=
  integrableOn_disk_of_bounded (measurable_gradInner f g).aestronglyMeasurable
    (M := 2 * (Df * Dg)) fun w hw => norm_gradInner_le_of_bounded (hDf w hw) (hDg w hw)

/-- AM–GM: `|a| + |b| ≤ δ + (a² + b²)/(2δ)`. -/
lemma abs_add_abs_le {a b δ : ℝ} (hδ : 0 < δ) : |a| + |b| ≤ δ + (a ^ 2 + b ^ 2) / (2 * δ) := by
  have ha : |a| ≤ (δ ^ 2 + a ^ 2) / (2 * δ) := by
    rw [le_div_iff₀ (by positivity)]; nlinarith [sq_nonneg (|a| - δ), sq_abs a, abs_nonneg a]
  have hb : |b| ≤ (δ ^ 2 + b ^ 2) / (2 * δ) := by
    rw [le_div_iff₀ (by positivity)]; nlinarith [sq_nonneg (|b| - δ), sq_abs b, abs_nonneg b]
  calc |a| + |b| ≤ (δ ^ 2 + a ^ 2) / (2 * δ) + (δ ^ 2 + b ^ 2) / (2 * δ) := add_le_add ha hb
    _ = δ + (a ^ 2 + b ^ 2) / (2 * δ) := by field_simp; ring

/-- The union of the `ε`-balls about the punctures. -/
def Uε (k : ℕ) (ε : ℝ) : Set ℂ := ⋃ p ∈ pF k, Metric.ball p ε

lemma measurableSet_Uε (k : ℕ) (ε : ℝ) : MeasurableSet (Uε k ε) :=
  Finset.measurableSet_biUnion _ fun _ _ => measurableSet_ball

lemma cutP_eq_one_of_notMem (hk : 1 ≤ k) {ε : ℝ} (h0 : 0 < ε) (h1 : ε < 1) {w : ℂ}
    (hw : w ∉ Uε k ε) : cutP k ε w = 1 := by
  refine cutP_eq_one hk h0 h1 fun p hp => ?_
  have : w ∉ Metric.ball p ε := fun h => hw (Set.mem_biUnion ((mem_pF hk).mpr hp) h)
  rw [Metric.mem_ball, dist_eq_norm] at this
  exact not_lt.mp this

/-- `1 − cutP² ≤ 1_{Uε}`. -/
lemma one_sub_cutP_sq_le (hk : 1 ≤ k) {ε : ℝ} (h0 : 0 < ε) (h1 : ε < 1) (w : ℂ) :
    1 - cutP k ε w ^ 2 ≤ (Uε k ε).indicator (fun _ => (1 : ℝ)) w := by
  by_cases hw : w ∈ Uε k ε
  · rw [Set.indicator_of_mem hw]
    nlinarith [cutP_nonneg k ε w]
  · rw [Set.indicator_of_notMem hw, cutP_eq_one_of_notMem hk h0 h1 hw]; norm_num

/-- The area of the puncture neighbourhoods: `≤ N π ε²`. -/
lemma volume_real_Uε_le (k : ℕ) {ε : ℝ} (h0 : 0 < ε) :
    (volume : Measure ℂ).real (Uε k ε) ≤ (pF k).card * (Real.pi * ε ^ 2) := by
  have h : volume (Uε k ε) ≤ ∑ p ∈ pF k, volume (Metric.ball p ε) :=
    measure_biUnion_finset_le _ _
  have hsum : ∑ p ∈ pF k, volume (Metric.ball p ε)
      = ENNReal.ofReal ((pF k).card * (Real.pi * ε ^ 2)) := by
    simp only [Complex.volume_ball, Finset.sum_const, nsmul_eq_mul]
    rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity),
      ENNReal.ofReal_pow h0.le, ENNReal.ofReal_natCast, ← NNReal.coe_real_pi,
      ENNReal.ofReal_coe_nnreal]
    ring
  rw [hsum] at h
  unfold Measure.real
  exact ENNReal.toReal_le_of_le_ofReal (by positivity) h

lemma volume_real_disk : (volume : Measure ℂ).real disk = Real.pi := by
  rw [Measure.real, disk, Complex.volume_ball]
  simp [NNReal.coe_real_pi]

/-- **`Bd`-continuity under the puncture cutoff, quantitative form.**  For `f, g` differentiable,
bounded, with bounded gradient on the disk, and any `δ > 0`:
`‖Bd(χf, χg) − Bd(f, g)‖ ≤ C₀·area(D ∩ Uε) + K·δ·π + (K/(2δ) + Mf·Mg)·E`, with
`E = ∫_D |∇χ|²`, `C₀ = 2 Df Dg + 8(k−1)² Mf Mg`, `K = Df Mg + Mf Dg`. -/
theorem Bd_cutoff_bound (hk : 2 ≤ k) {ε δ : ℝ} (h0 : 0 < ε) (h1 : ε < 1) (hδ : 0 < δ)
    {f g : ℂ → ℂ} {Mf Df Mg Dg : ℝ}
    (hf : ∀ w ∈ disk, DifferentiableAt ℝ f w) (hMf : ∀ w ∈ disk, ‖f w‖ ≤ Mf)
    (hDf : ∀ w ∈ disk, ‖fderiv ℝ f w‖ ≤ Df)
    (hg : ∀ w ∈ disk, DifferentiableAt ℝ g w) (hMg : ∀ w ∈ disk, ‖g w‖ ≤ Mg)
    (hDg : ∀ w ∈ disk, ‖fderiv ℝ g w‖ ≤ Dg) :
    ‖Bd k (cutMul (cutP k ε) f) (cutMul (cutP k ε) g) - Bd k f g‖
      ≤ (2 * (Df * Dg) + 8 * ((k : ℝ) - 1) ^ 2 * (Mf * Mg))
            * (volume : Measure ℂ).real (disk ∩ Uε k ε)
        + (Df * Mg + Mf * Dg) * (δ * Real.pi)
        + ((Df * Mg + Mf * Dg) / (2 * δ) + Mf * Mg) * ∫ w in disk, gradSq (cutPC k ε) w := by
  have hk1 : 1 ≤ k := by omega
  set χ := cutP k ε with hχ
  set K := Df * Mg + Mf * Dg with hK
  set C0 := 2 * (Df * Dg) + 8 * ((k : ℝ) - 1) ^ 2 * (Mf * Mg) with hC0
  set C1 := K / (2 * δ) + Mf * Mg with hC1
  have hχd : ∀ w, DifferentiableAt ℝ χ w := fun w =>
    ((cutP_contDiff k h0 h1).differentiable (by simp)) w
  have hχ0 : ∀ w, 0 ≤ χ w := cutP_nonneg k ε
  have hχ1 : ∀ w, χ w ≤ 1 := cutP_le_one k ε
  have h0d : (0 : ℂ) ∈ disk := by rw [mem_disk_iff]; simp
  have hMf0 : 0 ≤ Mf := le_trans (norm_nonneg _) (hMf 0 h0d)
  have hMg0 : 0 ≤ Mg := le_trans (norm_nonneg _) (hMg 0 h0d)
  have hDf0 : 0 ≤ Df := le_trans (norm_nonneg _) (hDf 0 h0d)
  have hDg0 : 0 ≤ Dg := le_trans (norm_nonneg _) (hDg 0 h0d)
  have hK0 : 0 ≤ K := by positivity
  have hC10 : 0 ≤ C1 := by positivity
  -- the cut-off functions on the disk
  have hfχ : ∀ w ∈ disk, DifferentiableAt ℝ (cutMul χ f) w := fun w hw =>
    (hasFDerivAt_cutMul (hχd w) (hf w hw)).differentiableAt
  have hgχ : ∀ w ∈ disk, DifferentiableAt ℝ (cutMul χ g) w := fun w hw =>
    (hasFDerivAt_cutMul (hχd w) (hg w hw)).differentiableAt
  have hMfχ : ∀ w ∈ disk, ‖cutMul χ f w‖ ≤ Mf := fun w hw => by
    unfold cutMul
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hχ0 w)]
    exact le_trans (mul_le_of_le_one_left (norm_nonneg _) (hχ1 w)) (hMf w hw)
  have hMgχ : ∀ w ∈ disk, ‖cutMul χ g w‖ ≤ Mg := fun w hw => by
    unfold cutMul
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hχ0 w)]
    exact le_trans (mul_le_of_le_one_left (norm_nonneg _) (hχ1 w)) (hMg w hw)
  -- abbreviations for the four densities
  set gI := gradInner f g with hgIdef
  set gIχ := gradInner (cutMul χ f) (cutMul χ g) with hgIχdef
  set pot : ℂ → ℂ := fun w => (potV k w : ℂ) * (starRingEnd ℂ) (f w) * g w with hpotdef
  set potχ : ℂ → ℂ := fun w =>
    (potV k w : ℂ) * (starRingEnd ℂ) (cutMul χ f w) * cutMul χ g w with hpotχdef
  -- the pointwise bound function
  set b : ℂ → ℝ := fun w => C0 * (Uε k ε).indicator (fun _ => (1 : ℝ)) w + K * δ
    + C1 * gradSq (cutPC k ε) w with hb
  have hgradχ : ∀ w, gradSq (cutPC k ε) w
      = (fderiv ℝ χ w 1) ^ 2 + (fderiv ℝ χ w I) ^ 2 := fun w => by
    rw [show cutPC k ε = fun z => (χ z : ℂ) from rfl, gradSq_ofReal (hχd w)]
    simp [Real.norm_eq_abs, sq_abs]
  have hpt : ∀ w ∈ disk, ‖(gIχ w - gI w) - (potχ w - pot w)‖ ≤ b w := by
    intro w hw
    have hG := gradInner_cutoff_bound (hχd w) (hf w hw) (hg w hw) (hχ0 w) (hχ1 w)
      (hMf w hw) (hDf w hw) (hMg w hw) (hDg w hw)
    have hP := potCross_cutoff_bound χ f g (potV k w) w (hχ0 w) (hχ1 w) (hMf w hw) (hMg w hw)
    have hind := one_sub_cutP_sq_le hk1 h0 h1 w
    have hgi := norm_gradInner_le_of_bounded (hDf w hw) (hDg w hw)
    have hV : |potV k w| ≤ 8 * ((k : ℝ) - 1) ^ 2 := by
      rw [abs_of_nonneg (potV_nonneg k w)]; exact potV_le hk (le_of_lt (mem_disk_iff.mp hw))
    have hamgm := abs_add_abs_le (a := fderiv ℝ χ w 1) (b := fderiv ℝ χ w I) hδ
    have hind0 : 0 ≤ (Uε k ε).indicator (fun _ => (1 : ℝ)) w :=
      Set.indicator_nonneg (fun _ _ => zero_le_one) _
    have e1 : (1 - χ w ^ 2) * ‖gI w‖
        ≤ (Uε k ε).indicator (fun _ => (1:ℝ)) w * (2 * (Df * Dg)) :=
      mul_le_mul hind hgi (norm_nonneg _) hind0
    have e2 : (1 - χ w ^ 2) * (|potV k w| * (Mf * Mg))
        ≤ (Uε k ε).indicator (fun _ => (1:ℝ)) w * (8 * ((k : ℝ) - 1) ^ 2 * (Mf * Mg)) :=
      mul_le_mul hind (by gcongr) (by positivity) hind0
    have e3 : K * (|fderiv ℝ χ w 1| + |fderiv ℝ χ w I|)
        ≤ K * (δ + ((fderiv ℝ χ w 1) ^ 2 + (fderiv ℝ χ w I) ^ 2) / (2 * δ)) :=
      mul_le_mul_of_nonneg_left hamgm hK0
    have e4 : K * (δ + ((fderiv ℝ χ w 1) ^ 2 + (fderiv ℝ χ w I) ^ 2) / (2 * δ))
        = K * δ + K / (2 * δ) * ((fderiv ℝ χ w 1) ^ 2 + (fderiv ℝ χ w I) ^ 2) := by
      field_simp
    have hbw : b w = C0 * (Uε k ε).indicator (fun _ => (1 : ℝ)) w + K * δ
        + C1 * ((fderiv ℝ χ w 1) ^ 2 + (fderiv ℝ χ w I) ^ 2) := by
      simp only [hb, hgradχ w]
    rw [hbw]
    refine le_trans (norm_sub_le _ _) ?_
    have hGw : ‖gIχ w - gI w‖ ≤ (1 - χ w ^ 2) * ‖gI w‖
        + K * (|fderiv ℝ χ w 1| + |fderiv ℝ χ w I|)
        + Mf * Mg * ((fderiv ℝ χ w 1) ^ 2 + (fderiv ℝ χ w I) ^ 2) := hG
    have hPw : ‖potχ w - pot w‖ ≤ (1 - χ w ^ 2) * (|potV k w| * (Mf * Mg)) := hP
    nlinarith [e1, e2, e3, e4, hGw, hPw, sq_nonneg (fderiv ℝ χ w 1), sq_nonneg (fderiv ℝ χ w I)]
  -- integrability on the disk
  have hE : Integrable (gradSq (cutPC k ε)) := integrable_gradSq_cutPC k h0 h1
  have hI1 : IntegrableOn (fun w => C0 * (Uε k ε).indicator (fun _ => (1 : ℝ)) w) disk :=
    ((integrableOn_const (C := (1 : ℝ)) (measure_ball_lt_top).ne).indicator
      (measurableSet_Uε k ε)).const_mul C0
  have hI2 : IntegrableOn (fun _ => K * δ) disk :=
    integrableOn_const (C := K * δ) (measure_ball_lt_top).ne
  have hI3 : IntegrableOn (fun w => C1 * gradSq (cutPC k ε) w) disk :=
    hE.integrableOn.const_mul C1
  have hbint : IntegrableOn b disk := (hI1.add hI2).add hI3
  have hgI : IntegrableOn gI disk := integrableOn_gradInner_bounded hDf hDg
  have hpot : IntegrableOn pot disk :=
    integrableOn_pot hk (continuousOn_of_diff hf) (continuousOn_of_diff hg) hMf hMg
  have hpotχ : IntegrableOn potχ disk :=
    integrableOn_pot hk (continuousOn_of_diff hfχ) (continuousOn_of_diff hgχ) hMfχ hMgχ
  have hgIχ : IntegrableOn gIχ disk := by
    refine ((hgI.norm.add hbint).add (hpotχ.norm.add hpot.norm)).mono'
      (measurable_gradInner _ _).aestronglyMeasurable ?_
    rw [ae_restrict_iff' measurableSet_disk]
    refine Eventually.of_forall fun w hw => ?_
    have t0 := hpt w hw
    have t1 := norm_le_norm_add_norm_sub' (gIχ w) (gI w)
    have t2 := norm_le_norm_add_norm_sub' (gIχ w - gI w) (potχ w - pot w)
    have t3 := norm_sub_le (potχ w) (pot w)
    simp only [Pi.add_apply]
    linarith
  -- assemble
  have hBd : Bd k (cutMul χ f) (cutMul χ g) - Bd k f g
      = ∫ w in disk, ((gIχ w - gI w) - (potχ w - pot w)) := by
    have i1 : IntegrableOn (fun w => gIχ w - gI w) disk := hgIχ.sub hgI
    have i2 : IntegrableOn (fun w => potχ w - pot w) disk := hpotχ.sub hpot
    rw [integral_sub i1 i2, integral_sub hgIχ hgI, integral_sub hpotχ hpot]
    unfold Bd
    ring
  have hbval : ∫ w in disk, b w
      = C0 * (volume : Measure ℂ).real (disk ∩ Uε k ε) + K * δ * Real.pi
        + C1 * ∫ w in disk, gradSq (cutPC k ε) w := by
    have i12 : IntegrableOn (fun w => C0 * (Uε k ε).indicator (fun _ => (1 : ℝ)) w + K * δ)
        disk := hI1.add hI2
    simp only [hb]
    rw [integral_add (f := fun w => C0 * (Uε k ε).indicator (fun _ => (1 : ℝ)) w + K * δ)
        (g := fun w => C1 * gradSq (cutPC k ε) w) i12 hI3,
      integral_add (f := fun w => C0 * (Uε k ε).indicator (fun _ => (1 : ℝ)) w)
        (g := fun _ => K * δ) hI1 hI2,
      integral_const_mul, integral_const_mul, setIntegral_indicator (measurableSet_Uε k ε),
      setIntegral_const, setIntegral_const, volume_real_disk]
    simp only [smul_eq_mul, mul_one]
    rw [integral_const_mul]
    ring
  rw [hBd]
  calc ‖∫ w in disk, ((gIχ w - gI w) - (potχ w - pot w))‖
      ≤ ∫ w in disk, ‖(gIχ w - gI w) - (potχ w - pot w)‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ w in disk, b w := by
        refine integral_mono_of_nonneg (Eventually.of_forall fun w => norm_nonneg _) hbint ?_
        exact (ae_restrict_iff' measurableSet_disk).mpr (Eventually.of_forall hpt)
    _ = _ := by rw [hbval]; ring

end KsIndex.CutoffContinuity
