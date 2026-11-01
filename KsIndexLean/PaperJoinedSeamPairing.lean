module

public import KsIndexLean.JoinedSeamPairing
public import KsIndexLean.SeamUnitPhaseTests

@[expose] public section


/-! Actual pair-radical vectors satisfy the two half-annulus identities for
their joined Sobolev fields, with no remaining representative hypotheses. -/
noncomputable section
open Set MeasureTheory
open scoped ContDiff
namespace KsIndex.Trace
open KsIndex.WeakH1 KsIndex.Surface

def joinedHalfResidual (u v : ComplexH1) (c : ℂ) (ψ : ℂ → ℂ) (s : Set ℂ) : ℂ :=
  (∫ z in s, jetPairing (joinedDiskJet u v c) ψ z) -
    ∫ z in s, (potV 3 z : ℂ) * starRingEnd ℂ (joinedDiskValue u v c z) * ψ z

lemma conj_seam_phase (α : ℝ) :
    starRingEnd ℂ (Complex.exp ((2 * Real.pi * α) * Complex.I)) =
      (Complex.exp ((2 * Real.pi * α) * Complex.I))⁻¹ := by
  rw [← Complex.exp_conj]
  simp only [map_mul, map_ofNat, Complex.conj_ofReal, Complex.conj_I,
    mul_neg, Complex.exp_neg]

end KsIndex.Trace
namespace KsIndex.PaperSlitTransport
open KsIndex.Trace KsIndex.WeakH1 KsIndex.PaperSlitAdapter

/-- The actual phase-joined field satisfies the split sesquilinear identity.
The phase in the joined VALUE is positive, while its conjugate in the form is inverse. -/
theorem pair_radical_joined_halves {α : ℝ} {j : ℕ}
    (u : paperSlitCharacterDomain α j) (hrad : ∀ w, Bpair u w = 0)
    {ψ : ℂ → ℂ} (hs : ContDiff ℝ ∞ ψ)
    (hi : ∀ w : ℂ, ‖w‖ ≤ 1 / 2 → ψ w = 0)
    (ho : ∀ w : ℂ, 2 ≤ ‖w‖ → ψ w = 0)
    (hsector : ∀ w : ℂ, ‖w‖ = 1 → 0 ≤ (w ^ 3).re → ψ w = 0) :
    joinedHalfResidual u.val.1 u.val.2 (Complex.exp ((2 * Real.pi * α) * Complex.I)) ψ
      innerHalfAnnulus +
    joinedHalfResidual u.val.1 u.val.2 (Complex.exp ((2 * Real.pi * α) * Complex.I)) ψ
      outerHalfAnnulus = 0 := by
  obtain ⟨f, g, hf, hg, ha, hb⟩ := pair_radical_smooth_representatives u hrad
  unfold joinedHalfResidual
  rw [joined_pairing_inner u.val.1 u.val.2 _ hf ha,
    joined_pairing_outer u.val.1 u.val.2 _ hg hb, conj_seam_phase]
  exact pair_radical_annulus_identity_all_tests u hrad hf hg ha hb hs hi ho hsector

/-- The complementary arcs use the phase-one joined field, for arbitrary domain phase α. -/
theorem pair_radical_joined_halves_one {α : ℝ} {j : ℕ}
    (u : paperSlitCharacterDomain α j) (hrad : ∀ w, Bpair u w = 0)
    {ψ : ℂ → ℂ} (hs : ContDiff ℝ ∞ ψ)
    (hi : ∀ w : ℂ, ‖w‖ ≤ 1 / 2 → ψ w = 0)
    (ho : ∀ w : ℂ, 2 ≤ ‖w‖ → ψ w = 0)
    (hsector : ∀ w : ℂ, ‖w‖ = 1 → (w ^ 3).re ≤ 0 → ψ w = 0) :
    joinedHalfResidual u.val.1 u.val.2 1 ψ innerHalfAnnulus +
    joinedHalfResidual u.val.1 u.val.2 1 ψ outerHalfAnnulus = 0 := by
  obtain ⟨f, g, hf, hg, ha, hb⟩ := pair_radical_smooth_representatives u hrad
  unfold joinedHalfResidual
  rw [joined_pairing_inner u.val.1 u.val.2 _ hf ha,
    joined_pairing_outer u.val.1 u.val.2 _ hg hb, map_one, one_mul]
  exact pair_radical_annulus_identity_one_all_tests u hrad hf hg ha hb hs hi ho hsector

end KsIndex.PaperSlitTransport
