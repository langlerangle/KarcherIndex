module

public import KsIndexLean.SeamDomainWeakGluing
public import KsIndexLean.LocalizedMollification
public import KsIndexLean.PhaseGermTrace
public import KsIndexLean.BoundarySmoothCore
public import KsIndexLean.SeamMollificationSupport

@[expose] public section


open Set MeasureTheory Filter Topology
open scoped ContDiff
noncomputable section
namespace KsIndex.Trace
open KsIndex.WeakH1 KsIndex.Bracket KsIndex.SingleDisk

/-- A smooth function across a seam determines two closed-disk representatives
with the prescribed phase. This identity does not require c to be a sign. -/
lemma phaseGerm_restricted_pair (c : ℂ) (hc : c ≠ 0) (F : ℂ → ℂ) :
    phaseGerm c (closedDiskRestriction F)
      (closedDiskRestriction (fun z => c⁻¹ * F (σ z))) = F := by
  funext z
  by_cases hz : ‖z‖ ≤ 1
  · simp only [phaseGerm, closedDiskRestriction, ite_eq_left hz]
  · have hn : 0 < ‖z‖ := lt_trans zero_lt_one (lt_of_not_ge hz)
    have hi : ‖σ z‖ ≤ 1 := by
      rw [norm_σ]
      exact (inv_le_one₀ hn).mpr (le_of_lt (lt_of_not_ge hz))
    simp only [phaseGerm, ite_eq_right hz, closedDiskRestriction, ite_eq_left hi, σ_σ]
    rw [← mul_assoc, mul_inv_cancel₀ hc, one_mul]

/-- The pair produced from a globally smooth seam function has a genuinely
smooth phase-gluing germ, not just matching trace values. -/
lemma phaseGerm_restricted_pair_smooth (c : ℂ) (hc : c ≠ 0) {F : ℂ → ℂ}
    (hF : ContDiff ℝ ∞ F) :
    ContDiff ℝ ∞ (phaseGerm c (closedDiskRestriction F)
      (closedDiskRestriction (fun z => c⁻¹ * F (σ z)))) := by
  rw [phaseGerm_restricted_pair c hc]
  exact hF

/-- Localize and mollify the actual two-sided phase-adjusted weak join.
Values and every directional derivative converge in whole-plane L2. The
subsequent pullback to two disk H1 carriers remains a separate step. -/
theorem localized_phase_pair_mollification {A : Set Circle₁} (hA : IsOpen A)
    (u v : ComplexH1) (c : ℂ) (hc0 : c ≠ 0)
    (hm : arcTrace A u = c • arcTrace A v) {χ : ℂ → ℝ}
    (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ)
    (hs : tsupport χ ⊆ (seamDomain A hA : Set ℂ)) :
    let w := fun z => χ z • joinedDiskValue u v c z
    let W := fun z => χ z • joinedDiskJet u v c z +
      (fderiv ℝ χ z).smulRight (joinedDiskValue u v c z)
    ∃ (hw : MemLp w 2 volume) (hW : ∀ d, MemLp (fun z => W z d) 2 volume)
      (fw : ℕ → Lp ℂ 2 (volume : Measure ℂ))
      (fW : ℕ → ℂ → Lp ℂ 2 (volume : Measure ℂ)),
      (∀ n, ContDiff ℝ ∞ (compactMollify (shrinkingMollifier n) w)) ∧
      (∀ n, ContDiff ℝ ∞
        (phaseGerm c (closedDiskRestriction (compactMollify (shrinkingMollifier n) w))
          (closedDiskRestriction (fun z => c⁻¹ * compactMollify (shrinkingMollifier n) w (σ z))))) ∧
      (∀ n, (fw n : ℂ → ℂ) =ᵐ[volume] compactMollify (shrinkingMollifier n) w) ∧
      (∀ n d, (fW n d : ℂ → ℂ) =ᵐ[volume]
        fun z => lineDeriv ℝ (compactMollify (shrinkingMollifier n) w) z d) ∧
      Tendsto fw atTop (𝓝 (hw.toLp w)) ∧
      ∀ d, Tendsto (fun n => fW n d) atTop (𝓝 ((hW d).toLp (fun z => W z d))) := by
  have hL d : MemLp (fun z => joinedDiskJet u v c z d) 2
      (volume.restrict (seamDomain A hA : Set ℂ)) :=
    (seamDomain_jet_memLp hA u v c).continuousLinearMap_comp
      (ContinuousLinearMap.apply ℝ ℂ d)
  obtain ⟨hw, hW, fw, fW, hsm, hv, hd, ht, htD⟩ :=
    localized_mollification hχ hc hs (seamDomain_weak_gluing hA u v c hm)
      (seamDomain_value_memLp hA u v c) hL shrinkingMollifier_radius
  exact ⟨hw, hW, fw, fW, hsm,
    fun n => phaseGerm_restricted_pair_smooth c hc0 (hsm n), hv, hd, ht, htD⟩

end KsIndex.Trace
