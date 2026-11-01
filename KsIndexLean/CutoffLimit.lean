module

/-
The cutoff-limit step for the faithful finite-energy injection.

Fatou supplies a finite nonnegative Lebesgue integral BEFORE integrability of the
uncut density is concluded. No monotonicity or separate measurability of the
cutoffs is assumed. This module is independent of EnergySmooth and Caccioppoli.
-/
public import KsIndexLean.PunctureCutoffP
public import Mathlib.MeasureTheory.Integral.Bochner.Basic

@[expose] public section


noncomputable section

open MeasureTheory Filter Topology

namespace KsIndex.FaithfulInjection

open KsIndex.Surface KsIndex.PunctureCutoff

/-- Uniformly bounded integrable cutoff energies give an integrable limiting
density, with the same bound. The proof uses Fatou, not monotone convergence. -/
theorem integrableOn_of_cutoff_bound {g : ℂ → ℝ} {χ : ℕ → ℂ → ℝ} {K : ℝ}
    (hg : AEStronglyMeasurable g (volume.restrict disk))
    (hgn : ∀ w ∈ disk, 0 ≤ g w)
    (hχ : ∀ w ∈ disk, Tendsto (fun j => χ j w) atTop (𝓝 1))
    (hi : ∀ j, IntegrableOn (fun w => (χ j w) ^ 2 * g w) disk)
    (hK : ∀ j, (∫ w in disk, (χ j w) ^ 2 * g w) ≤ K) :
    IntegrableOn g disk ∧ (∫ w in disk, g w) ≤ K := by
  have hnn : 0 ≤ᵐ[volume.restrict disk] g :=
    ae_restrict_of_forall_mem Metric.isOpen_ball.measurableSet hgn
  have hfn (j : ℕ) : 0 ≤ᵐ[volume.restrict disk] (fun w => (χ j w) ^ 2 * g w) := by
    filter_upwards [hnn] with w hw
    exact mul_nonneg (sq_nonneg _) hw
  have hK0 : 0 ≤ K := (integral_nonneg_of_ae (hfn 0)).trans (hK 0)
  have hconv : ∀ᵐ w ∂volume.restrict disk,
      Tendsto (fun j => ENNReal.ofReal ((χ j w) ^ 2 * g w)) atTop
        (𝓝 (ENNReal.ofReal (g w))) := by
    refine ae_restrict_of_forall_mem Metric.isOpen_ball.measurableSet fun w hw => ?_
    have ht : Tendsto (fun j => (χ j w) ^ 2 * g w) atTop (𝓝 (g w)) := by
      simpa using ((hχ w hw).pow 2).mul_const (g w)
    exact ENNReal.continuous_ofReal.continuousAt.tendsto.comp ht
  have hbound (j : ℕ) :
      (∫⁻ w in disk, ENNReal.ofReal ((χ j w) ^ 2 * g w)) ≤ ENNReal.ofReal K := by
    rw [← ofReal_integral_eq_lintegral_ofReal (hi j) (hfn j)]
    exact ENNReal.ofReal_le_ofReal (hK j)
  have hfatou : (∫⁻ w in disk, ENNReal.ofReal (g w)) ≤ ENNReal.ofReal K := by
    calc
      _ = ∫⁻ w in disk, liminf (fun j => ENNReal.ofReal ((χ j w) ^ 2 * g w)) atTop := by
        apply lintegral_congr_ae
        filter_upwards [hconv] with w hw
        exact hw.liminf_eq.symm
      _ ≤ liminf (fun j => ∫⁻ w in disk, ENNReal.ofReal ((χ j w) ^ 2 * g w)) atTop :=
        lintegral_liminf_le' (fun j => (hi j).aestronglyMeasurable.aemeasurable.ennreal_ofReal)
      _ ≤ ENNReal.ofReal K :=
        liminf_le_of_frequently_le' (Eventually.of_forall hbound).frequently
  have hgi : IntegrableOn g disk :=
    (lintegral_ofReal_ne_top_iff_integrable hg hnn).mp
      (ne_of_lt (lt_of_le_of_lt hfatou ENNReal.ofReal_lt_top))
  refine ⟨hgi, ?_⟩
  apply (ENNReal.ofReal_le_ofReal_iff hK0).mp
  rwa [ofReal_integral_eq_lintegral_ofReal hgi hnn]

/-- A fixed sequence in `(0, exp(-1)]` approaching zero. -/
def cutoffEps (j : ℕ) : ℝ := Real.exp (-((j : ℝ) + 1))

lemma cutoffEps_pos (j : ℕ) : 0 < cutoffEps j := Real.exp_pos _

lemma cutoffEps_le_exp_neg_one (j : ℕ) : cutoffEps j ≤ Real.exp (-1) := by
  apply Real.exp_le_exp.mpr
  have : (0 : ℝ) ≤ j := Nat.cast_nonneg j
  linarith

lemma cutoffEps_lt_one (j : ℕ) : cutoffEps j < 1 := by
  apply (cutoffEps_le_exp_neg_one j).trans_lt
  exact Real.exp_lt_one_iff.mpr (by norm_num)

lemma cutoffEps_tendsto_zero : Tendsto cutoffEps atTop (𝓝 0) := by
  have ht : Tendsto (fun j : ℕ => (j : ℝ) + 1) atTop atTop := by
    simpa only [Function.comp_def, Nat.cast_add, Nat.cast_one] using
      (tendsto_natCast_atTop_atTop (R := ℝ)).comp (tendsto_add_atTop_nat 1)
  exact Real.tendsto_exp_neg_atTop_nhds_zero.comp ht

/-- At any open-disk point, all finitely many punctures are eventually farther
away than the cutoff radius. In particular the cutoff is eventually exactly 1. -/
lemma cutP_eventually_eq_one {k : ℕ} (hk : 1 ≤ k) {w : ℂ} (hw : w ∈ disk) :
    ∀ᶠ j : ℕ in atTop, cutP k (cutoffEps j) w = 1 := by
  have hdist : ∀ p ∈ pF k, ∀ᶠ j : ℕ in atTop, cutoffEps j ≤ ‖w - p‖ := by
    intro p hp
    have hwp : w ≠ p := by
      intro heq
      subst w
      exact punctures_notMem_disk hk hw ((mem_pF hk).mp hp)
    have hpos : 0 < ‖w - p‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hwp)
    exact (cutoffEps_tendsto_zero.eventually (gt_mem_nhds hpos)).mono fun _ h => h.le
  filter_upwards [(eventually_all_finset (pF k)).mpr hdist] with j hj
  apply cutP_eq_one hk (cutoffEps_pos j) (cutoffEps_lt_one j)
  intro p hp
  exact hj p ((mem_pF hk).mpr hp)

lemma cutP_tendsto_one {k : ℕ} (hk : 1 ≤ k) {w : ℂ} (hw : w ∈ disk) :
    Tendsto (fun j => cutP k (cutoffEps j) w) atTop (𝓝 1) := by
  apply tendsto_const_nhds.congr'
  filter_upwards [cutP_eventually_eq_one hk hw] with j hj
  exact hj.symm

/-- The paper's puncture-cutoff adapter. Only the uniformly bounded, already
integrable truncated densities are supplied by the Caccioppoli argument. -/
theorem integrableOn_of_cutP_bound {k : ℕ} (hk : 1 ≤ k) {g : ℂ → ℝ} {K : ℝ}
    (hg : AEStronglyMeasurable g (volume.restrict disk))
    (hgn : ∀ w ∈ disk, 0 ≤ g w)
    (hi : ∀ j, IntegrableOn (fun w => (cutP k (cutoffEps j) w) ^ 2 * g w) disk)
    (hK : ∀ j, (∫ w in disk, (cutP k (cutoffEps j) w) ^ 2 * g w) ≤ K) :
    IntegrableOn g disk ∧ (∫ w in disk, g w) ≤ K :=
  integrableOn_of_cutoff_bound hg hgn (fun _ hw => cutP_tendsto_one hk hw) hi hK

end KsIndex.FaithfulInjection
