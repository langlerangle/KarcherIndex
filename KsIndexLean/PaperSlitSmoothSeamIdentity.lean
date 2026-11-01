module

public import KsIndexLean.PaperSlitInteriorSmooth
public import KsIndexLean.SeamStraddleIdentity

@[expose] public section


/-!
# Smooth representatives and the averaged seam identity

An element of the radical of `Bpair` on `paperSlitCharacterDomain α j` admits
representatives smooth on the open disk and equal almost everywhere there to
its two component values. Their weak derivative agreement follows from the
smooth representative theorem.

These representatives satisfy `AveragedSeamIdentity`: a pairing identity on the
inner and outer half-annuli with the explicit test `straddleAverage j ψ` and
inverse phase factor. The test vanishes on the specified inner, outer and
unit-circle sector sets. This is an identity for that averaged test family,
not a statement of the weak equation for arbitrary tests across the seam.
-/
noncomputable section
open Set MeasureTheory
open scoped ContDiff
namespace KsIndex.PaperSlitTransport
open KsIndex.Trace KsIndex.WeakH1 KsIndex.PaperSlitAdapter
open KsIndex.GradOrtho KsIndex.Surface

/-- The seam pairing identity with its explicit averaged test and inverse phase. -/
def AveragedSeamIdentity (α : ℝ) (j : ℕ) (f g : ℂ → ℂ) : Prop :=
  ∀ ψ : ℂ → ℂ, ContDiff ℝ ∞ ψ →
    (∀ w : ℂ, ‖w‖ ≤ 1 / 2 → ψ w = 0) →
    (∀ w : ℂ, 2 ≤ ‖w‖ → ψ w = 0) →
    (∀ w : ℂ, ‖w‖ = 1 → 0 ≤ (w ^ 3).re → ψ w = 0) →
    ((∫ z in innerHalfAnnulus, gradInner f (straddleAverage j ψ) z) -
        ∫ z in innerHalfAnnulus, (potV 3 z : ℂ) * starRingEnd ℂ (f z) *
          straddleAverage j ψ z) +
      (Complex.exp ((2 * Real.pi * α) * Complex.I))⁻¹ *
        ((∫ w in outerHalfAnnulus, gradInner (g ∘ Bracket.σ) (straddleAverage j ψ) w) -
          ∫ w in outerHalfAnnulus, (potV 3 w : ℂ) *
            starRingEnd ℂ ((g ∘ Bracket.σ) w) * straddleAverage j ψ w) = 0

/-- Any smooth open-disk representatives of a radical element satisfy the averaged seam
identity; their weak derivative agreement is proved, not an extra input. -/
theorem averagedSeamIdentity_of_smooth_representatives {α : ℝ} {j : ℕ}
    (u : paperSlitCharacterDomain α j) (hrad : ∀ w, Bpair u w = 0)
    {f g : ℂ → ℂ}
    (hf : ContDiffOn ℝ (⊤ : ℕ∞) f (WeakH1.disk : Set ℂ))
    (hg : ContDiffOn ℝ (⊤ : ℕ∞) g (WeakH1.disk : Set ℂ))
    (ha : valueCLM u.val.1 =ᵐ[volume.restrict (WeakH1.disk : Set ℂ)] f)
    (hb : valueCLM u.val.2 =ᵐ[volume.restrict (WeakH1.disk : Set ℂ)] g) :
    AveragedSeamIdentity α j f g := by
  obtain ⟨hfx, hfy⟩ := Weq.disk_smooth_representative_derivatives u.val.1 hf ha
  obtain ⟨hgx, hgy⟩ := Weq.disk_smooth_representative_derivatives u.val.2 hg hb
  have hsub : innerHalfAnnulus ⊆ (WeakH1.disk : Set ℂ) := by
    intro z hz
    exact Metric.mem_ball.mpr (by simpa only [dist_zero_right] using hz.2)
  have hmono := ae_mono (Measure.restrict_mono (μ := (volume : Measure ℂ)) hsub le_rfl)
  intro ψ hs hi ho hsector
  exact pair_radical_annulus_identity_average u hrad hs hi ho hsector
    (ha.filter_mono hmono) (hfx.filter_mono hmono) (hfy.filter_mono hmono)
    (fun z hz => (hg.contDiffAt (WeakH1.disk.isOpen.mem_nhds (hsub hz))).differentiableAt
      (by simp))
    (hb.filter_mono hmono) (hgx.filter_mono hmono) (hgy.filter_mono hmono)

/-- A radical element supplies smooth open-disk representatives, their almost-everywhere
value agreement, and their averaged seam identity. -/
theorem pair_radical_exists_smooth_seam_identity {α : ℝ} {j : ℕ}
    (u : paperSlitCharacterDomain α j) (hrad : ∀ w, Bpair u w = 0) :
    ∃ f g : ℂ → ℂ,
      ContDiffOn ℝ (⊤ : ℕ∞) f (WeakH1.disk : Set ℂ) ∧
      ContDiffOn ℝ (⊤ : ℕ∞) g (WeakH1.disk : Set ℂ) ∧
      valueCLM u.val.1 =ᵐ[volume.restrict (WeakH1.disk : Set ℂ)] f ∧
      valueCLM u.val.2 =ᵐ[volume.restrict (WeakH1.disk : Set ℂ)] g ∧
      AveragedSeamIdentity α j f g := by
  obtain ⟨f, g, hf, hg, ha, hb⟩ := pair_radical_smooth_representatives u hrad
  exact ⟨f, g, hf, hg, ha, hb,
    averagedSeamIdentity_of_smooth_representatives u hrad hf hg ha hb⟩

end KsIndex.PaperSlitTransport
