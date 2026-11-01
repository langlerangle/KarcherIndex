module

/-
Transfer of L² convergence from a collar to a disk under support conditions.

The general restriction theorem transfers convergence on `A` to `D` when the
sequence and limit eventually agree almost everywhere on `D \ A`, with the stated
`MemLp` hypotheses on both sets. It requires no containment between the sets.
The disk/collar specialization assumes eventual collar support of the sequence
and almost-everywhere vanishing of the limit on the inner half-disk.

Proof contribution: Harmonic's Aristotle, submitted by Astra on 2026-09-16 and
ported by Kai on 2026-09-18. The returned development used Lean 4.28.0 and
Mathlib revision 8f9d9cff; the repository's current toolchain is specified separately.
-/
public import Mathlib

@[expose] public section

open Set MeasureTheory Filter Topology
open scoped ENNReal
noncomputable section
namespace AstraAristotle

/-- Auxiliary estimate: if `h` vanishes a.e. on `D \ A`, then the `L^p` seminorm of `h` over `D`
is bounded by its `L^p` seminorm over `A`, with no containment assumption between `D` and `A`. -/
theorem eLpNorm_restrict_le_of_ae_eq_zero_on_diff
    {α : Type*} [MeasurableSpace α] {μ : Measure α} {E : Type*} [NormedAddCommGroup E]
    {A D : Set α} (hA : MeasurableSet A) {h : α → E} {p : ℝ≥0∞} (hp0 : p ≠ 0) (hp : p ≠ ∞)
    (h0 : ∀ᵐ z ∂μ.restrict (D \ A), h z = 0) :
    eLpNorm h p (μ.restrict D) ≤ eLpNorm h p (μ.restrict A) := by
  by_cases hmA : AEStronglyMeasurable h (μ.restrict A)
  · have hmI : AEStronglyMeasurable h (μ.restrict (D ∩ A)) :=
      hmA.mono_measure (Measure.restrict_mono inter_subset_right le_rfl)
    have hmDiff : AEStronglyMeasurable h (μ.restrict (D \ A)) :=
      (aestronglyMeasurable_const (b := (0 : E))).congr
        (Filter.EventuallyEq.symm h0)
    have hmD := hmI.add_measure hmDiff
    rw [Measure.restrict_inter_add_sdiff D hA] at hmD
    rw [eLpNorm_eq_eLpNorm' hp0 hp hmD, eLpNorm_eq_eLpNorm' hp0 hp hmA,
      eLpNorm', eLpNorm']
    refine ENNReal.rpow_le_rpow ?_ (by positivity)
    have hzero : ∫⁻ a, ‖h a‖ₑ ^ p.toReal ∂(μ.restrict (D \ A)) = 0 := by
      have hae : ∀ᵐ a ∂(μ.restrict (D \ A)), ‖h a‖ₑ ^ p.toReal = 0 := by
        filter_upwards [h0] with a ha
        simp [ha, ENNReal.zero_rpow_of_pos (ENNReal.toReal_pos hp0 hp)]
      simpa using lintegral_congr_ae hae
    calc ∫⁻ a, ‖h a‖ₑ ^ p.toReal ∂(μ.restrict D)
        = ∫⁻ a, ‖h a‖ₑ ^ p.toReal ∂(μ.restrict (D ∩ A)) +
          ∫⁻ a, ‖h a‖ₑ ^ p.toReal ∂(μ.restrict (D \ A)) := by
          rw [← lintegral_add_measure, Measure.restrict_inter_add_diff _ hA]
      _ ≤ ∫⁻ a, ‖h a‖ₑ ^ p.toReal ∂(μ.restrict A) := by
          rw [hzero, add_zero]
          exact lintegral_mono' (Measure.restrict_mono inter_subset_right le_rfl) le_rfl
  · rw [eLpNorm_of_not_aestronglyMeasurable hmA]
    exact le_top

/-- L2 convergence on A controls D when the differences vanish off A in D.
No containment D subset A is assumed. -/
theorem supported_restriction_tendsto
    {A D : Set ℂ} (hA : MeasurableSet A) (hD : MeasurableSet D)
    {f : ℕ → ℂ → ℂ} {g : ℂ → ℂ}
    (hfA : ∀ n, MemLp (f n) 2 (volume.restrict A))
    (hgA : MemLp g 2 (volume.restrict A))
    (hfD : ∀ n, MemLp (f n) 2 (volume.restrict D))
    (hgD : MemLp g 2 (volume.restrict D))
    (hz : ∀ᶠ n in atTop, ∀ᵐ z ∂volume.restrict (D \ A), f n z = g z)
    (ht : Tendsto (fun n => (hfA n).toLp (f n)) atTop (𝓝 (hgA.toLp g))) :
    Tendsto (fun n => (hfD n).toLp (f n)) atTop (𝓝 (hgD.toLp g)) := by
  rw [Lp.tendsto_Lp_iff_tendsto_eLpNorm'' _ hfA _ hgA] at ht
  rw [Lp.tendsto_Lp_iff_tendsto_eLpNorm'' _ hfD _ hgD]
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds ht
    (Eventually.of_forall fun n => zero_le) ?_
  filter_upwards [hz] with n hn
  refine eLpNorm_restrict_le_of_ae_eq_zero_on_diff hA (by simp) (by simp) ?_
  filter_upwards [hn] with z hzn
  simp [Pi.sub_apply, hzn]

/-- Collar L² convergence implies disk L² convergence under eventual collar support
and almost-everywhere vanishing of the limit on the inner half-disk. -/
theorem collar_supported_disk_tendsto
    {f : ℕ → ℂ → ℂ} {g : ℂ → ℂ}
    (hfA : ∀ n, MemLp (f n) 2 (volume.restrict {z : ℂ | 1/2 < ‖z‖ ∧ ‖z‖ < 2}))
    (hgA : MemLp g 2 (volume.restrict {z : ℂ | 1/2 < ‖z‖ ∧ ‖z‖ < 2}))
    (hfD : ∀ n, MemLp (f n) 2 (volume.restrict (Metric.ball (0 : ℂ) 1)))
    (hgD : MemLp g 2 (volume.restrict (Metric.ball (0 : ℂ) 1)))
    (hs : ∀ᶠ n in atTop, tsupport (f n) ⊆ {z : ℂ | 1/2 < ‖z‖ ∧ ‖z‖ < 2})
    (hg : ∀ᵐ z ∂volume.restrict (Metric.ball (0 : ℂ) 1), ‖z‖ ≤ 1/2 → g z = 0)
    (ht : Tendsto (fun n => (hfA n).toLp (f n)) atTop (𝓝 (hgA.toLp g))) :
    Tendsto (fun n => (hfD n).toLp (f n)) atTop (𝓝 (hgD.toLp g)) := by
  set A : Set ℂ := {z : ℂ | 1/2 < ‖z‖ ∧ ‖z‖ < 2} with hAdef
  have hAopen : IsOpen A :=
    (isOpen_lt continuous_const continuous_norm).inter (isOpen_lt continuous_norm continuous_const)
  have hA : MeasurableSet A := hAopen.measurableSet
  have hD : MeasurableSet (Metric.ball (0 : ℂ) 1) := measurableSet_ball
  refine supported_restriction_tendsto hA hD hfA hgA hfD hgD ?_ ht
  -- off the collar, inside the unit disk, both `f n` and `g` vanish a.e.
  have hgdiff : ∀ᵐ z ∂volume.restrict (Metric.ball (0 : ℂ) 1 \ A), ‖z‖ ≤ 1/2 → g z = 0 :=
    ae_mono (Measure.restrict_mono diff_subset le_rfl) hg
  have hmem : ∀ᵐ z ∂volume.restrict (Metric.ball (0 : ℂ) 1 \ A), z ∈ Metric.ball (0 : ℂ) 1 \ A :=
    ae_restrict_mem (hD.diff hA)
  filter_upwards [hs] with n hn
  filter_upwards [hgdiff, hmem] with z hz hzmem
  have hz1 : ‖z‖ < 1 := by simpa [Complex.dist_eq] using hzmem.1
  have hznotA : z ∉ A := hzmem.2
  have hzle : ‖z‖ ≤ 1/2 := by
    by_contra hlt
    exact hznotA ⟨lt_of_not_ge hlt, hz1.trans (by norm_num)⟩
  have hfz : f n z = 0 := by
    have : z ∉ tsupport (f n) := fun hmemt => hznotA (hn hmemt)
    exact image_eq_zero_of_notMem_tsupport this
  rw [hfz, hz hzle]

end AstraAristotle
