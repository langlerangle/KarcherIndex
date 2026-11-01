module

public import KsIndexLean.PaperSeamWeakEquation
public import KsIndexLean.WeakInteriorSmooth
public import KsIndexLean.WeakSmoothGluing

@[expose] public section


/-! Smooth representatives across both actual paper seam families, derived
from the radical condition and the trace-domain membership. -/
noncomputable section
open Set MeasureTheory
open scoped BoundedContinuousFunction
namespace KsIndex.Trace
open KsIndex.WeakH1 KsIndex.Surface

lemma joined_potential_memLp_general (k : ℕ) (hk : 2 ≤ k) {A : Set Circle₁} (hA : IsOpen A)
    (u v : ComplexH1) (c : ℂ) :
    MemLp (fun z => (potV k z : ℂ) * joinedDiskValue u v c z) 2
      (volume.restrict (seamDomain A hA : Set ℂ)) := by
  have hV := Complex.ofRealCLM.contDiff.comp (contDiff_potV hk)
  obtain ⟨C, hC⟩ := (isCompact_closedBall (0 : ℂ) 2).exists_bound_of_continuousOn
    hV.continuous.continuousOn
  have hu := seamDomain_value_memLp hA u v c
  apply hu.of_le_mul (c := C) (hV.continuous.aestronglyMeasurable.mul hu.aestronglyMeasurable)
  filter_upwards [ae_restrict_mem (seamDomain A hA).isOpen.measurableSet] with z hz
  change ‖(potV k z : ℂ) * joinedDiskValue u v c z‖ ≤ _
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_right
    (hC z (Metric.mem_closedBall.mpr (by simpa only [dist_zero_right] using hz.1.2.le)))
    (norm_nonneg _)

theorem joined_exists_smooth_near_general (k : ℕ) (hk : 2 ≤ k) {A : Set Circle₁} (hA : IsOpen A)
    (u v : ComplexH1) (c : ℂ) (hm : arcTrace A u = c • arcTrace A v)
    (heq : Weq.InteriorWeakEquation (seamDomain A hA)
      (fun z => joinedDiskJet u v c z 1) (fun z => joinedDiskJet u v c z Complex.I)
      (fun z => (potV k z : ℂ) * joinedDiskValue u v c z))
    {z : ℂ} (hz : z ∈ seamDomain A hA) :
    ∃ r : ℝ, 0 < r ∧ Metric.ball z r ⊆ (seamDomain A hA : Set ℂ) ∧ ∃ g : ℂ →ᵇ ℂ,
      ContDiff ℝ (⊤ : ℕ∞) (g : ℂ → ℂ) ∧
      joinedDiskValue u v c =ᵐ[volume.restrict (Metric.ball z r)] g := by
  have hw := seamDomain_weak_gluing hA u v c hm
  have hJ := seamDomain_jet_memLp hA u v c
  exact Weq.exists_smooth_near_of_interior_weak_jet
    (seamDomain_value_memLp hA u v c)
    (hJ.continuousLinearMap_comp (ContinuousLinearMap.apply ℝ ℂ 1))
    (hJ.continuousLinearMap_comp (ContinuousLinearMap.apply ℝ ℂ Complex.I))
    (joined_potential_memLp_general k hk hA u v c) (hw.hasWeakLineDerivOn 1)
    (hw.hasWeakLineDerivOn Complex.I) heq
    (Complex.ofRealCLM.contDiff.comp (contDiff_potV hk)) hz

lemma joined_potential_memLp {A : Set Circle₁} (hA : IsOpen A)
    (u v : ComplexH1) (c : ℂ) :
    MemLp (fun z => (potV 3 z : ℂ) * joinedDiskValue u v c z) 2
      (volume.restrict (seamDomain A hA : Set ℂ)) :=
  joined_potential_memLp_general 3 (by decide) hA u v c

theorem joined_exists_smooth_near {A : Set Circle₁} (hA : IsOpen A)
    (u v : ComplexH1) (c : ℂ) (hm : arcTrace A u = c • arcTrace A v)
    (heq : Weq.InteriorWeakEquation (seamDomain A hA)
      (fun z => joinedDiskJet u v c z 1) (fun z => joinedDiskJet u v c z Complex.I)
      (fun z => (potV 3 z : ℂ) * joinedDiskValue u v c z))
    {z : ℂ} (hz : z ∈ seamDomain A hA) :
    ∃ r : ℝ, 0 < r ∧ Metric.ball z r ⊆ (seamDomain A hA : Set ℂ) ∧ ∃ g : ℂ →ᵇ ℂ,
      ContDiff ℝ (⊤ : ℕ∞) (g : ℂ → ℂ) ∧
      joinedDiskValue u v c =ᵐ[volume.restrict (Metric.ball z r)] g :=
  joined_exists_smooth_near_general 3 (by decide) hA u v c hm heq hz

/-- A matching pair with the full joined weak equation has one smooth
representative across the open matching arcs, for every k ≥ 2. -/
theorem joined_smooth_representative_general (k : ℕ) (hk : 2 ≤ k)
    {A : Set Circle₁} (hA : IsOpen A) (u v : ComplexH1) (c : ℂ)
    (hm : arcTrace A u = c • arcTrace A v)
    (heq : Weq.InteriorWeakEquation (seamDomain A hA)
      (fun z => joinedDiskJet u v c z 1) (fun z => joinedDiskJet u v c z Complex.I)
      (fun z => (potV k z : ℂ) * joinedDiskValue u v c z)) :
    ∃ F : ℂ → ℂ, ContDiffOn ℝ (⊤ : ℕ∞) F (seamDomain A hA : Set ℂ) ∧
      joinedDiskValue u v c =ᵐ[volume.restrict (seamDomain A hA : Set ℂ)] F := by
  apply Weq.exists_contDiffOn_ae_of_smooth_near
  intro z hz
  obtain ⟨r, hr, hs, g, hg, ha⟩ :=
    joined_exists_smooth_near_general k hk hA u v c hm heq hz
  exact ⟨r, hr, hs, g, hg, ha⟩

end KsIndex.Trace
namespace KsIndex.PaperSlitTransport
open KsIndex.Trace KsIndex.PaperSlitAdapter

/-- A smooth representative on the entire phase seam domain, including its matching arcs. -/
theorem pair_radical_seam_smooth_representative {α : ℝ} {j : ℕ}
    (u : paperSlitCharacterDomain α j) (hrad : ∀ w, Bpair u w = 0) :
    ∃ F : ℂ → ℂ,
      ContDiffOn ℝ (⊤ : ℕ∞) F
        (seamDomain (boundaryArc 3 0) (isOpen_boundaryArc 3 0) : Set ℂ) ∧
      joinedDiskValue u.val.1 u.val.2 (Complex.exp ((2 * Real.pi * α) * Complex.I))
        =ᵐ[volume.restrict (seamDomain (boundaryArc 3 0) (isOpen_boundaryArc 3 0) : Set ℂ)] F := by
  apply Weq.exists_contDiffOn_ae_of_smooth_near
  intro z hz
  have hm := (mem_slitTraceDomain 3 _ u.val).mp u.property.1
  obtain ⟨r, hr, hs, g, hg, ha⟩ := joined_exists_smooth_near (isOpen_boundaryArc 3 0)
    u.val.1 u.val.2 _ hm.2 (pair_radical_seam_weak_equation u hrad) hz
  exact ⟨r, hr, hs, g, hg, ha⟩

/-- The complementary matching arcs admit a smooth phase-one joined representative. -/
theorem pair_radical_seam_one_smooth_representative {α : ℝ} {j : ℕ}
    (u : paperSlitCharacterDomain α j) (hrad : ∀ w, Bpair u w = 0) :
    ∃ F : ℂ → ℂ,
      ContDiffOn ℝ (⊤ : ℕ∞) F
        (seamDomain (boundaryArc 3 1) (isOpen_boundaryArc 3 1) : Set ℂ) ∧
      joinedDiskValue u.val.1 u.val.2 1
        =ᵐ[volume.restrict (seamDomain (boundaryArc 3 1) (isOpen_boundaryArc 3 1) : Set ℂ)] F := by
  apply Weq.exists_contDiffOn_ae_of_smooth_near
  intro z hz
  have hm := (mem_slitTraceDomain 3 _ u.val).mp u.property.1
  obtain ⟨r, hr, hs, g, hg, ha⟩ := joined_exists_smooth_near (isOpen_boundaryArc 3 1)
    u.val.1 u.val.2 1 (by simpa only [one_smul] using hm.1)
    (pair_radical_seam_one_weak_equation u hrad) hz
  exact ⟨r, hr, hs, g, hg, ha⟩

end KsIndex.PaperSlitTransport
