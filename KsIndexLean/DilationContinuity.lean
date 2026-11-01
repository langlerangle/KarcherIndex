module

public import KsIndexLean.WeakH1Adapter
public import Mathlib.MeasureTheory.Function.ContinuousMapDense
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional

@[expose] public section


/-!
# L² continuity under dilation

For `g ∈ L²(ℂ)` and real scalars `c n ≥ 1` converging to `1`, the functions
`z ↦ g (c n • z)` converge to `g` in the L² seminorm. Monotonicity of the
sequence is not required.

The proof uses the exact planar scaling factor `|r|⁻¹` for nonzero real
scalars, density of compactly supported continuous functions, and dominated
convergence on a common support ball. This is a whole-plane L² result;
trace and boundary approximation arguments belong to its consumers.
-/

open Set MeasureTheory Filter Topology
open scoped ENNReal
noncomputable section
namespace KsIndex.Trace

/-- Exact L² scaling of a dilation: on `ℂ` (real dimension 2),
`‖g (r • ·)‖₂ = |r|⁻¹ ‖g‖₂`. -/
lemma eLpNorm_comp_smul {g : ℂ → ℂ} (hg : AEStronglyMeasurable g volume)
    {r : ℝ} (hr : r ≠ 0) :
    eLpNorm (fun z => g (r • z)) 2 volume =
      ENNReal.ofReal |r|⁻¹ * eLpNorm g 2 volume := by
  have hmap := Measure.map_addHaar_smul (μ := (volume : Measure ℂ)) hr
  have hgmap : AEStronglyMeasurable g
      (Measure.map (fun z : ℂ => r • z) (volume : Measure ℂ)) := by
    rw [hmap]
    exact hg.smul_measure _
  have hgcomp : AEStronglyMeasurable (fun z : ℂ => g (r • z)) volume :=
    hgmap.comp_aemeasurable (measurable_const_smul r).aemeasurable
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num) hgcomp,
      eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num) hg]
  have hae : AEMeasurable (fun w => ‖g w‖ₑ ^ (2 : ℝ≥0∞).toReal)
      (Measure.map (r • ·) (volume : Measure ℂ)) := by
    rw [hmap]
    exact (hg.enorm.pow_const _).smul_measure _
  have hcov : ∫⁻ z, ‖g (r • z)‖ₑ ^ (2 : ℝ≥0∞).toReal ∂volume =
      ENNReal.ofReal |(r ^ 2 : ℝ)|⁻¹ *
        ∫⁻ w, ‖g w‖ₑ ^ (2 : ℝ≥0∞).toReal ∂volume := by
    calc ∫⁻ z, ‖g (r • z)‖ₑ ^ (2 : ℝ≥0∞).toReal ∂volume
        = ∫⁻ w, ‖g w‖ₑ ^ (2 : ℝ≥0∞).toReal
            ∂(Measure.map (r • ·) (volume : Measure ℂ)) :=
          (lintegral_map' hae (measurable_const_smul r).aemeasurable).symm
      _ = ENNReal.ofReal |(r ^ 2 : ℝ)|⁻¹ *
            ∫⁻ w, ‖g w‖ₑ ^ (2 : ℝ≥0∞).toReal ∂volume := by
          rw [hmap]
          simp [lintegral_smul_measure, Complex.finrank_real_complex]
  rw [hcov, ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0:ℝ) ≤ 1 / (2 : ℝ≥0∞).toReal)]
  congr 1
  have habs : |(r ^ 2 : ℝ)|⁻¹ = (|r|⁻¹) ^ 2 := by
    rw [abs_pow, inv_pow]
  rw [habs, ENNReal.ofReal_pow (by positivity),
    ← ENNReal.rpow_natCast (ENNReal.ofReal |r|⁻¹) 2, ← ENNReal.rpow_mul]
  norm_num

/-- Dilations preserve L² membership. -/
lemma MemLp.comp_smul {g : ℂ → ℂ} (hg : MemLp g 2 volume) {r : ℝ} (hr : r ≠ 0) :
    MemLp (fun z => g (r • z)) 2 volume := by
  rw [memLp_iff, eLpNorm_comp_smul hg.aestronglyMeasurable hr]
  exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top hg.eLpNorm_lt_top

/-- Middle term of the three-term split: for a continuous compactly supported
`φ`, the dilated difference tends to `0` in L² by dominated convergence on the
common support ball (`c n ≥ 1` keeps the dilated support inside the ball). -/
lemma tendsto_eLpNorm_dilation_sub_of_continuous {φ : ℂ → ℂ}
    (hφcont : Continuous φ) (hφc : HasCompactSupport φ)
    {c : ℕ → ℝ} (hc1 : ∀ n, 1 ≤ c n) (hc : Tendsto c atTop (𝓝 1)) :
    Tendsto (fun n => eLpNorm (fun z => φ (c n • z) - φ z) 2 volume)
      atTop (𝓝 0) := by
  obtain ⟨C, hC⟩ := hφc.exists_bound_of_continuous hφcont
  obtain ⟨R, hR⟩ := hφc.isCompact.isBounded.subset_closedBall (0 : ℂ)
  set F : ℕ → ℂ → ℝ≥0∞ :=
    fun n z => ‖φ (c n • z) - φ z‖ₑ ^ (2 : ℕ) with hFdef
  have hφn : ∀ n, Continuous fun z => φ (c n • z) :=
    fun n => hφcont.comp (continuous_const_smul (c n))
  have hFmeas : ∀ n, Measurable (F n) := fun n =>
    (((hφn n).sub hφcont).enorm).measurable.pow_const _
  set B : ℝ≥0∞ := ENNReal.ofReal (2 * C) with hBdef
  set bound : ℂ → ℝ≥0∞ :=
    (Metric.closedBall (0 : ℂ) R).indicator (fun _ => B ^ (2 : ℕ)) with hbdef
  have hzero : ∀ n z, z ∉ Metric.closedBall (0 : ℂ) R → F n z = 0 := by
    intro n z hz
    have hzR : R < ‖z‖ := by
      simpa [Metric.mem_closedBall, dist_zero_right, not_le] using hz
    have h1 : φ z = 0 := by
      apply image_eq_zero_of_notMem_tsupport
      intro hm
      have := hR hm
      simp only [Metric.mem_closedBall, dist_zero_right] at this
      linarith
    have h2 : φ (c n • z) = 0 := by
      apply image_eq_zero_of_notMem_tsupport
      intro hm
      have hle := hR hm
      simp only [Metric.mem_closedBall, dist_zero_right] at hle
      have hnorm : ‖c n • z‖ = c n * ‖z‖ := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos (lt_of_lt_of_le one_pos (hc1 n))]
      have hzn : ‖z‖ ≤ c n * ‖z‖ := by
        nlinarith [norm_nonneg z, hc1 n]
      rw [hnorm] at hle
      linarith
    simp only [hFdef]
    rw [h2, h1, sub_zero]
    simp
  have hbound : ∀ n, F n ≤ᵐ[volume] bound := by
    intro n
    apply Eventually.of_forall
    intro z
    by_cases hz : z ∈ Metric.closedBall (0 : ℂ) R
    · have hb : ∀ x : ℂ, ‖φ x‖ₑ ≤ ENNReal.ofReal C := fun x => by
        rw [← ofReal_norm]
        exact ENNReal.ofReal_le_ofReal (hC x)
      have hle : ‖φ (c n • z) - φ z‖ₑ ≤ B := by
        calc ‖φ (c n • z) - φ z‖ₑ ≤ ‖φ (c n • z)‖ₑ + ‖φ z‖ₑ := enorm_sub_le
          _ ≤ ENNReal.ofReal C + ENNReal.ofReal C := add_le_add (hb _) (hb _)
          _ = B := by
              rw [hBdef, ← ENNReal.ofReal_add (le_trans (norm_nonneg _) (hC 0))
                (le_trans (norm_nonneg _) (hC 0))]
              ring_nf
      calc F n z ≤ B ^ (2 : ℕ) := by exact pow_le_pow_left' hle 2
        _ = bound z := by simp [hbdef, hz]
    · simp [hzero n z hz, hbdef, hz]
  have hbfin : ∫⁻ z, bound z ∂volume ≠ ⊤ := by
    rw [hbdef, lintegral_indicator Metric.isClosed_closedBall.measurableSet]
    simp only [setLIntegral_const]
    exact (ENNReal.mul_lt_top (ENNReal.pow_lt_top ENNReal.ofReal_lt_top)
      measure_closedBall_lt_top).ne
  have hlim : ∀ᵐ z ∂(volume : Measure ℂ),
      Tendsto (fun n => F n z) atTop (𝓝 0) := by
    apply Eventually.of_forall
    intro z
    have hcz : Tendsto (fun n => c n • z) atTop (𝓝 z) := by
      have := hc.smul_const z
      simpa [one_smul] using this
    have hφz : Tendsto (fun n => φ (c n • z) - φ z) atTop (𝓝 0) := by
      have := ((hφcont.tendsto z).comp hcz).sub
        (tendsto_const_nhds : Tendsto (fun _ : ℕ => φ z) atTop (𝓝 (φ z)))
      simpa [Function.comp_def] using this
    have henorm : Tendsto (fun n => ‖φ (c n • z) - φ z‖ₑ) atTop (𝓝 0) := by
      have := (continuous_enorm.tendsto (0 : ℂ)).comp hφz
      simpa [Function.comp_def, enorm_zero] using this
    have hpow := ENNReal.Tendsto.pow (n := 2) henorm
    simp only [hFdef]
    simpa using hpow
  have hI : Tendsto (fun n => ∫⁻ z, F n z ∂volume) atTop (𝓝 0) := by
    have := tendsto_lintegral_of_dominated_convergence bound hFmeas hbound hbfin
      (by simpa using hlim)
    simpa using this
  rw [ENNReal.tendsto_nhds_zero]
  intro ε hε
  have hε2 : (0 : ℝ≥0∞) < ε ^ (2 : ℕ) := by positivity
  filter_upwards [(ENNReal.tendsto_nhds_zero.mp hI) _ hε2] with n hn
  have ht : (2 : ℝ≥0∞).toReal = ((2 : ℕ) : ℝ) := by norm_num
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)
    (show AEStronglyMeasurable (fun z => φ (c n • z) - φ z) volume from
      ((hφn n).sub hφcont).aestronglyMeasurable)]
  simp only [ht, ENNReal.rpow_natCast]
  calc (∫⁻ z, ‖φ (c n • z) - φ z‖ₑ ^ (2 : ℕ) ∂volume) ^ (1 / ((2 : ℕ) : ℝ))
      ≤ (ε ^ (2 : ℕ)) ^ (1 / ((2 : ℕ) : ℝ)) := by
        exact ENNReal.rpow_le_rpow hn (by norm_num)
    _ = ε := by
        rw [← ENNReal.rpow_natCast ε 2, ← ENNReal.rpow_mul]
        norm_num

/-- **L² dilation continuity from above.** For `g ∈ L²(ℂ)`, `cₙ ≥ 1`, and `cₙ → 1`,
`g (cₙ • ·) → g` in the L² seminorm: three-term split through a compactly
supported continuous approximant; the dilated approximation error scales by `|cₙ|⁻¹ ≤ 1`
(`eLpNorm_comp_smul`), the middle term is
`tendsto_eLpNorm_dilation_sub_of_continuous`. -/
theorem tendsto_eLpNorm_dilation_sub {g : ℂ → ℂ} (hg : MemLp g 2 volume)
    {c : ℕ → ℝ} (hc1 : ∀ n, 1 ≤ c n) (hc : Tendsto c atTop (𝓝 1)) :
    Tendsto (fun n => eLpNorm (fun z => g (c n • z) - g z) 2 volume)
      atTop (𝓝 0) := by
  rw [ENNReal.tendsto_nhds_zero]
  intro ε hε
  have hε3 : ε / 3 ≠ 0 := by
    simp only [ne_eq, ENNReal.div_eq_zero_iff, not_or]
    exact ⟨hε.ne', by norm_num⟩
  obtain ⟨φ, hφc, hφe, hφcont, hφmem⟩ :=
    hg.exists_hasCompactSupport_eLpNorm_sub_le (by norm_num) hε3
  have hmid := tendsto_eLpNorm_dilation_sub_of_continuous hφcont hφc hc1 hc
  filter_upwards [(ENNReal.tendsto_nhds_zero.mp hmid) _ (pos_iff_ne_zero.mpr hε3)]
    with n hn
  have hcn0 : c n ≠ 0 := (lt_of_lt_of_le one_pos (hc1 n)).ne'
  have hgφ : AEStronglyMeasurable (g - φ) volume :=
    hg.aestronglyMeasurable.sub hφcont.aestronglyMeasurable
  have hsplit : (fun z => g (c n • z) - g z) =
      fun z => (g - φ) (c n • z) + ((φ (c n • z) - φ z) + (φ - g) z) := by
    funext z
    simp only [Pi.sub_apply]
    ring
  rw [hsplit]
  have h1m : AEStronglyMeasurable (fun z => (g - φ) (c n • z)) volume := by
    have := hgφ.comp_quasiMeasurePreserving
      (Measure.quasiMeasurePreserving_smul (μ := (volume : Measure ℂ)) hcn0)
    simpa [Function.comp_def] using this
  have h2m : AEStronglyMeasurable (fun z => φ (c n • z) - φ z) volume :=
    ((hφcont.comp (continuous_const_smul (c n))).sub hφcont).aestronglyMeasurable
  have h3m : AEStronglyMeasurable (fun z => (φ - g) z) volume :=
    hφcont.aestronglyMeasurable.sub hg.aestronglyMeasurable
  calc eLpNorm
        (fun z => (g - φ) (c n • z) + ((φ (c n • z) - φ z) + (φ - g) z)) 2 volume
      ≤ eLpNorm (fun z => (g - φ) (c n • z)) 2 volume +
        eLpNorm (fun z => (φ (c n • z) - φ z) + (φ - g) z) 2 volume :=
        eLpNorm_add_le (by norm_num)
    _ ≤ eLpNorm (fun z => (g - φ) (c n • z)) 2 volume +
        (eLpNorm (fun z => φ (c n • z) - φ z) 2 volume +
          eLpNorm (fun z => (φ - g) z) 2 volume) := by
        gcongr
        exact eLpNorm_add_le (by norm_num)
    _ ≤ ε / 3 + (ε / 3 + ε / 3) := by
        gcongr
        · rw [eLpNorm_comp_smul hgφ hcn0]
          calc ENNReal.ofReal |c n|⁻¹ * eLpNorm (g - φ) 2 volume
              ≤ 1 * eLpNorm (g - φ) 2 volume := by
                gcongr
                rw [← ENNReal.ofReal_one]
                apply ENNReal.ofReal_le_ofReal
                rw [abs_of_pos (lt_of_lt_of_le one_pos (hc1 n))]
                exact inv_le_one_of_one_le₀ (hc1 n)
            _ ≤ ε / 3 := by rw [one_mul]; exact hφe
        · have hcomm : eLpNorm (fun z => (φ - g) z) 2 volume =
              eLpNorm (g - φ) 2 volume := by
            apply eLpNorm_sub_comm
          rw [hcomm]
          exact hφe
    _ = ε := by rw [← add_assoc, ENNReal.add_thirds]

end KsIndex.Trace
