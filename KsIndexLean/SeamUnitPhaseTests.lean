module

public import KsIndexLean.SeamRemoveAverage

@[expose] public section


/-! The complementary seam arcs have phase one. Tests vanish on the opposite
closed sector; the domain's arbitrary phase is then immaterial on that sector
because both traces vanish. -/
noncomputable section
open Set MeasureTheory
open scoped ContDiff
namespace KsIndex.PaperSlitTransport
open KsIndex.Trace KsIndex.WeakH1 KsIndex.PaperSlitAdapter KsIndex.Bracket

lemma straddlePair_one_mem_paperSlit (α : ℝ) {ψ : ℂ → ℂ}
    (hs : ContDiff ℝ ∞ ψ)
    (hi : ∀ w : ℂ, ‖w‖ ≤ 1 / 2 → ψ w = 0)
    (ho : ∀ w : ℂ, 2 ≤ ‖w‖ → ψ w = 0)
    (hsector : ∀ w : ℂ, ‖w‖ = 1 → (w ^ 3).re ≤ 0 → ψ w = 0) :
    straddlePair 1 hs hi ho ∈ paperSlitDomain α := by
  have hcircle : ∀ w : Circle₁, ψ (σ (w : ℂ)) = ψ (w : ℂ) := fun w => by
    rw [σ_self (mem_sphere_zero_iff_norm.mp w.property)]
  have harc : ∀ w : Circle₁, w ∈ boundaryArc 3 0 → ψ (w : ℂ) = 0 := by
    intro w hw
    have hh := (mem_boundaryArc 3 0 w).mp hw
    have hn : ((w : ℂ) ^ 3).re < 0 := by simpa using hh
    exact hsector w (mem_sphere_zero_iff_norm.mp w.property) hn.le
  change straddlePair 1 hs hi ho ∈ slitTraceDomain 3 _
  rw [mem_slitTraceDomain]
  have hpair : straddlePair 1 hs hi ho =
      (globalSmoothH1 ψ hs, globalSmoothH1 (fun z => ψ (σ z)) (straddle_pull_smooth hs hi ho)) := by
    simp [straddlePair]
  rw [hpair]
  constructor
  · exact globalSmoothH1_arcTrace_congr _ hs _ (fun w => (hcircle w).symm)
  · have h1 : arcTrace (boundaryArc 3 0) (globalSmoothH1 ψ hs) = 0 :=
      globalSmoothH1_zeroTrace_of_vanish (measurableSet_boundaryArc 3 0) hs harc
    have h2 : arcTrace (boundaryArc 3 0)
        (globalSmoothH1 (fun z => ψ (σ z)) (straddle_pull_smooth hs hi ho)) = 0 :=
      globalSmoothH1_zeroTrace_of_vanish (measurableSet_boundaryArc 3 0) _
        (fun w hw => (hcircle w).trans (harc w hw))
    simp only [h1, h2, smul_zero]

lemma straddleAverage_opposite_sector (j : ℕ) {ψ : ℂ → ℂ}
    (hsector : ∀ w : ℂ, ‖w‖ = 1 → (w ^ 3).re ≤ 0 → ψ w = 0)
    (w : ℂ) (hw : ‖w‖ = 1) (hre : (w ^ 3).re ≤ 0) : straddleAverage j ψ w = 0 := by
  have hn : ∀ z : ℂ, ‖planeRotation (-(2 * Real.pi) / 3) z‖ = ‖z‖ :=
    (planeRotation (-(2 * Real.pi) / 3)).norm_map
  have hcube : ∀ z : ℂ, ((planeRotation (-(2 * Real.pi) / 3) z) ^ 3).re = (z ^ 3).re := by
    intro z
    rw [planeRotation_apply, mul_pow, rotUnit_third_cubed, one_mul]
  simp only [straddleAverage, hsector w hw hre,
    hsector _ ((hn w).trans hw) (by rw [hcube]; exact hre),
    hsector _ (((hn _).trans (hn w)).trans hw) (by rw [hcube, hcube]; exact hre),
    mul_zero, add_zero]

/-- Unrestricted smooth straddling tests on the phase-one arcs. No test
character is assumed, and the paper domain may have any phase on the other arcs. -/
theorem pair_radical_straddle_one_all_tests {α : ℝ} {j : ℕ}
    (u : paperSlitCharacterDomain α j) (hrad : ∀ w, Bpair u w = 0)
    {ψ : ℂ → ℂ} (hs : ContDiff ℝ ∞ ψ)
    (hi : ∀ w : ℂ, ‖w‖ ≤ 1 / 2 → ψ w = 0)
    (ho : ∀ w : ℂ, 2 ≤ ‖w‖ → ψ w = 0)
    (hsector : ∀ w : ℂ, ‖w‖ = 1 → (w ^ 3).re ≤ 0 → ψ w = 0) :
    weakJacobi (surfacePotential 3) u.val.1 (globalSmoothH1 ψ hs) +
      weakJacobi (surfacePotential 3) u.val.2
        (globalSmoothH1 (fun z => ψ (σ z)) (straddle_pull_smooth hs hi ho)) = 0 := by
  have hm : straddlePair 1 (straddleAverage_smooth j hs)
      (straddleAverage_in j hi) (straddleAverage_out j ho) ∈ paperSlitCharacterDomain α j :=
    ⟨straddlePair_one_mem_paperSlit α (straddleAverage_smooth j hs)
      (straddleAverage_in j hi) (straddleAverage_out j ho) (straddleAverage_opposite_sector j hsector),
     straddlePair_mem_pairCharacter 1 (straddleAverage_smooth j hs)
      (straddleAverage_in j hi) (straddleAverage_out j ho) _ _ (straddleAverage_char j ψ)⟩
  have h := hrad ⟨_, hm⟩
  change weakJacobi (surfacePotential 3) u.val.1 (globalSmoothH1 _ _) +
    weakJacobi (surfacePotential 3) u.val.2 ((1 : ℂ)⁻¹ • globalSmoothH1 _ _) = 0 at h
  simp only [inv_one, one_smul] at h
  have hemb : globalSmoothH1 (fun z => straddleAverage j ψ (σ z))
      (straddle_pull_smooth (straddleAverage_smooth j hs)
        (straddleAverage_in j hi) (straddleAverage_out j ho)) =
      globalSmoothH1 (straddleAverage j (fun z => ψ (σ z)))
        (straddleAverage_smooth j (straddle_pull_smooth hs hi ho)) := by
    congr 1
    exact straddleAverage_sigma j ψ
  rw [hemb, weakJacobi_straddleAverage j u.val.1 u.property.2.1 hs,
    weakJacobi_straddleAverage j u.val.2 u.property.2.2 (straddle_pull_smooth hs hi ho)] at h
  linear_combination (1 / 3 : ℂ) * h

/-- The unaveraged annulus identity for actual smooth disk representatives.
Only the geometric support restrictions remain on the test. -/
theorem pair_radical_annulus_identity_one_all_tests {α : ℝ} {j : ℕ}
    (u : paperSlitCharacterDomain α j) (hrad : ∀ w, Bpair u w = 0)
    {f g ψ : ℂ → ℂ}
    (hf : ContDiffOn ℝ (⊤ : ℕ∞) f (disk : Set ℂ))
    (hg : ContDiffOn ℝ (⊤ : ℕ∞) g (disk : Set ℂ))
    (ha : valueCLM u.val.1 =ᵐ[volume.restrict (disk : Set ℂ)] f)
    (hb : valueCLM u.val.2 =ᵐ[volume.restrict (disk : Set ℂ)] g)
    (hs : ContDiff ℝ ∞ ψ)
    (hi : ∀ w : ℂ, ‖w‖ ≤ 1 / 2 → ψ w = 0)
    (ho : ∀ w : ℂ, 2 ≤ ‖w‖ → ψ w = 0)
    (hsector : ∀ w : ℂ, ‖w‖ = 1 → (w ^ 3).re ≤ 0 → ψ w = 0) :
    ((∫ z in innerHalfAnnulus, KsIndex.GradOrtho.gradInner f ψ z) -
        ∫ z in innerHalfAnnulus, (KsIndex.Surface.potV 3 z : ℂ) * starRingEnd ℂ (f z) * ψ z) +
      ((∫ w in outerHalfAnnulus, KsIndex.GradOrtho.gradInner (g ∘ Bracket.σ) ψ w) -
          ∫ w in outerHalfAnnulus, (KsIndex.Surface.potV 3 w : ℂ) *
            starRingEnd ℂ ((g ∘ Bracket.σ) w) * ψ w) = 0 := by
  obtain ⟨hfx, hfy⟩ := Weq.disk_smooth_representative_derivatives u.val.1 hf ha
  obtain ⟨hgx, hgy⟩ := Weq.disk_smooth_representative_derivatives u.val.2 hg hb
  have hsub : innerHalfAnnulus ⊆ (disk : Set ℂ) := by
    intro z hz
    exact Metric.mem_ball.mpr (by simpa only [dist_zero_right] using hz.2)
  have hm := ae_mono (Measure.restrict_mono (μ := (volume : Measure ℂ)) hsub le_rfl)
  have h := pair_radical_straddle_one_all_tests u hrad hs hi ho hsector
  rw [weakJacobi_inner_localized u.val.1 hs (fun z hz => hi z hz.le)
    (ha.filter_mono hm) (hfx.filter_mono hm) (hfy.filter_mono hm)] at h
  rw [weakJacobi_straddle_outer_rep u.val.2 hs hi ho
    (fun z hz => (hg.contDiffAt (disk.isOpen.mem_nhds (hsub hz))).differentiableAt (by simp))
    (hb.filter_mono hm) (hgx.filter_mono hm) (hgy.filter_mono hm)] at h
  exact h

end KsIndex.PaperSlitTransport
