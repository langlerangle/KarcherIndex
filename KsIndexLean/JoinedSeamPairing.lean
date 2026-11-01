module

public import KsIndexLean.JoinedSmoothRepresentatives
public import KsIndexLean.SeamInversionTransport

@[expose] public section


/-! The sesquilinear integrals of the actual joined field agree with the
smooth half-annulus formulas. Conjugation of the outer field phase is explicit. -/
noncomputable section
open Set MeasureTheory
namespace KsIndex.Trace
open KsIndex.WeakH1 KsIndex.GradOrtho KsIndex.Surface

/-- The first-jet Dirichlet pairing, with conjugation on the field slot. -/
def jetPairing (J : ℂ → ℂ →L[ℝ] ℂ) (ψ : ℂ → ℂ) (z : ℂ) : ℂ :=
  starRingEnd ℂ (J z 1) * fderiv ℝ ψ z 1 +
    starRingEnd ℂ (J z Complex.I) * fderiv ℝ ψ z Complex.I

lemma joined_pairing_inner_general (k : ℕ) (u v : ComplexH1) (c : ℂ) {f : ℂ → ℂ}
    (hf : ContDiffOn ℝ (⊤ : ℕ∞) f (WeakH1.disk : Set ℂ))
    (ha : valueCLM u =ᵐ[volume.restrict (WeakH1.disk : Set ℂ)] f)
    (ψ : ℂ → ℂ) :
    (∫ z in innerHalfAnnulus, jetPairing (joinedDiskJet u v c) ψ z) -
      (∫ z in innerHalfAnnulus, (potV k z : ℂ) *
        starRingEnd ℂ (joinedDiskValue u v c z) * ψ z) =
    (∫ z in innerHalfAnnulus, gradInner f ψ z) -
      ∫ z in innerHalfAnnulus, (potV k z : ℂ) * starRingEnd ℂ (f z) * ψ z := by
  congr 1
  · apply integral_congr_ae
    filter_upwards [joinedDiskJet_inner_representative u v c hf ha] with z hz
    simp only [jetPairing, hz, gradInner]
  · apply integral_congr_ae
    filter_upwards [joinedDiskValue_inner_representative u v c ha] with z hz
    rw [hz]

lemma joined_pairing_inner (u v : ComplexH1) (c : ℂ) {f : ℂ → ℂ}
    (hf : ContDiffOn ℝ (⊤ : ℕ∞) f (WeakH1.disk : Set ℂ))
    (ha : valueCLM u =ᵐ[volume.restrict (WeakH1.disk : Set ℂ)] f)
    (ψ : ℂ → ℂ) :
    (∫ z in innerHalfAnnulus, jetPairing (joinedDiskJet u v c) ψ z) -
      (∫ z in innerHalfAnnulus, (potV 3 z : ℂ) *
        starRingEnd ℂ (joinedDiskValue u v c z) * ψ z) =
    (∫ z in innerHalfAnnulus, gradInner f ψ z) -
      ∫ z in innerHalfAnnulus, (potV 3 z : ℂ) * starRingEnd ℂ (f z) * ψ z :=
  joined_pairing_inner_general 3 u v c hf ha ψ


lemma joined_pairing_outer_general (k : ℕ) (u v : ComplexH1) (c : ℂ) {g : ℂ → ℂ}
    (hg : ContDiffOn ℝ (⊤ : ℕ∞) g (WeakH1.disk : Set ℂ))
    (ha : valueCLM v =ᵐ[volume.restrict (WeakH1.disk : Set ℂ)] g)
    (ψ : ℂ → ℂ) :
    (∫ z in outerHalfAnnulus, jetPairing (joinedDiskJet u v c) ψ z) -
      (∫ z in outerHalfAnnulus, (potV k z : ℂ) *
        starRingEnd ℂ (joinedDiskValue u v c z) * ψ z) =
    starRingEnd ℂ c * ((∫ z in outerHalfAnnulus, gradInner (g ∘ Bracket.σ) ψ z) -
      ∫ z in outerHalfAnnulus, (potV k z : ℂ) *
        starRingEnd ℂ ((g ∘ Bracket.σ) z) * ψ z) := by
  rw [mul_sub, ← integral_const_mul, ← integral_const_mul]
  congr 1
  · apply integral_congr_ae
    filter_upwards [joinedDiskJet_outer_representative u v c hg ha,
      ae_restrict_mem (measurableSet_annulusSet (a := 1) (b := 2))] with z hz hza
    have hn : z ≠ 0 := norm_pos_iff.mp (lt_trans zero_lt_one hza.1)
    have hd : DifferentiableAt ℝ (g ∘ Bracket.σ) z :=
      ((hg.contDiffAt (WeakH1.disk.isOpen.mem_nhds
        (sigma_mem_disk_of_one_lt_norm hza.1))).comp z
        (Bracket.contDiffAt_σ hn)).differentiableAt (by simp)
    have he := fderiv_const_mul hd c
    change fderiv ℝ (fun z => c * g (Bracket.σ z)) z = _ at he
    simp only [jetPairing, hz, he, smul_apply, smul_eq_mul,
      map_mul, gradInner]
    ring
  · apply integral_congr_ae
    filter_upwards [joinedDiskValue_outer_representative u v c ha] with z hz
    simp only [hz, map_mul, Function.comp_apply]
    ring


lemma joined_pairing_outer (u v : ComplexH1) (c : ℂ) {g : ℂ → ℂ}
    (hg : ContDiffOn ℝ (⊤ : ℕ∞) g (WeakH1.disk : Set ℂ))
    (ha : valueCLM v =ᵐ[volume.restrict (WeakH1.disk : Set ℂ)] g)
    (ψ : ℂ → ℂ) :
    (∫ z in outerHalfAnnulus, jetPairing (joinedDiskJet u v c) ψ z) -
      (∫ z in outerHalfAnnulus, (potV 3 z : ℂ) *
        starRingEnd ℂ (joinedDiskValue u v c z) * ψ z) =
    starRingEnd ℂ c * ((∫ z in outerHalfAnnulus, gradInner (g ∘ Bracket.σ) ψ z) -
      ∫ z in outerHalfAnnulus, (potV 3 z : ℂ) *
        starRingEnd ℂ ((g ∘ Bracket.σ) z) * ψ z) :=
  joined_pairing_outer_general 3 u v c hg ha ψ

end KsIndex.Trace
