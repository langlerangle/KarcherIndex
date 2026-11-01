module

public import KsIndexLean.EnergySmoothWeakCopy
public import KsIndexLean.CollarBound

@[expose] public section


/-! Base-copy operator-norm energy, derived from EnergySmooth's existing
directional-derivative L² bounds rather than added as a hypothesis. -/
noncomputable section
open Set MeasureTheory
open scoped ENNReal
namespace KsIndex.EndChart
open KsIndex.Trace KsIndex.FaithfulInjection

theorem energySmooth_fderiv_memLp {k m : ℕ} (u : GradEnergySmooth k m)
    (n : ZMod (2*m)) :
    MemLp (fderiv ℝ (u.val n)) 2 (volume.restrict (KsIndex.WeakH1.disk : Set ℂ)) := by
  obtain ⟨hx, hy⟩ := energySmooth_direction_memLp u n
  have hs := hx.norm.add hy.norm
  apply hs.of_le (measurable_fderiv ℝ (u.val n)).aestronglyMeasurable.restrict
  apply Filter.Eventually.of_forall
  intro z
  simpa only [Pi.add_apply, Real.norm_eq_abs, abs_of_nonneg (add_nonneg (norm_nonneg _) (norm_nonneg _))]
    using (KsIndex.CollarBound.opNorm_le_components (fderiv ℝ (u.val n) z) le_rfl le_rfl)

theorem energySmooth_fderiv_energy_ne_top {k m : ℕ} (u : GradEnergySmooth k m)
    (n : ZMod (2*m)) :
    (∫⁻ z in (KsIndex.WeakH1.disk : Set ℂ),
      ENNReal.ofReal (‖fderiv ℝ (u.val n) z‖ ^ 2) ∂volume) ≠ ⊤ := by
  have h := lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top
    (by norm_num : (2 : ℝ≥0∞) ≠ 0) (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)
    (energySmooth_fderiv_memLp u n).eLpNorm_lt_top
  have heq : (fun z => ENNReal.ofReal (‖fderiv ℝ (u.val n) z‖ ^ 2)) =
      (fun z => ‖fderiv ℝ (u.val n) z‖ₑ ^ (2 : ℝ≥0∞).toReal) := by
    funext z
    simp [ENNReal.ofReal_pow, enorm]
  rw [heq]
  exact h.ne

/-- Contractive real projections (in particular Re and Im) preserve the base
energy bound, in the linear-map form used by chart transport. -/
theorem energySmooth_projected_energy_ne_top {k m : ℕ} (u : GradEnergySmooth k m)
    (n : ZMod (2*m)) (L : ℂ →L[ℝ] ℝ) (hL : ‖L‖ ≤ 1) :
    (∫⁻ z in (KsIndex.WeakH1.disk : Set ℂ),
      ENNReal.ofReal (‖L.comp (fderiv ℝ (u.val n) z)‖ ^ 2) ∂volume) ≠ ⊤ := by
  apply ne_top_of_le_ne_top (energySmooth_fderiv_energy_ne_top u n)
  apply lintegral_mono
  intro z
  apply ENNReal.ofReal_le_ofReal
  apply pow_le_pow_left₀ (norm_nonneg _)
  calc ‖L.comp (fderiv ℝ (u.val n) z)‖ ≤ ‖L‖ * ‖fderiv ℝ (u.val n) z‖ :=
        L.opNorm_comp_le _
    _ ≤ 1 * ‖fderiv ℝ (u.val n) z‖ :=
        mul_le_mul_of_nonneg_right hL (norm_nonneg _)
    _ = ‖fderiv ℝ (u.val n) z‖ := one_mul _

end KsIndex.EndChart
