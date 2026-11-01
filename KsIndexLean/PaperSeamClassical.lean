module

public import KsIndexLean.PaperSeamSmooth
public import KsIndexLean.WeakRepresentativeEquation

@[expose] public section


/-! Smooth classical Jacobi representatives on the actual paper seam domains. -/
noncomputable section
open Set MeasureTheory
namespace KsIndex.Trace
open KsIndex.WeakH1 KsIndex.Surface

/-- A trace-matched weak solution has a smooth classical representative on
its entire open seam domain, for arbitrary k ≥ 2. -/
theorem joined_classical_representative_general (k : ℕ) (hk : 2 ≤ k)
    {A : Set Circle₁} (hA : IsOpen A) (u v : ComplexH1) (c : ℂ)
    (hm : arcTrace A u = c • arcTrace A v)
    (heq : Weq.InteriorWeakEquation (seamDomain A hA)
      (fun z => joinedDiskJet u v c z 1) (fun z => joinedDiskJet u v c z Complex.I)
      (fun z => (potV k z : ℂ) * joinedDiskValue u v c z)) :
    ∃ F : ℂ → ℂ, ContDiffOn ℝ (⊤ : ℕ∞) F (seamDomain A hA : Set ℂ) ∧
      joinedDiskValue u v c =ᵐ[volume.restrict (seamDomain A hA : Set ℂ)] F ∧
      ∀ z ∈ seamDomain A hA, laplacian F z + (potV k z : ℂ) * F z = 0 := by
  obtain ⟨F, hF, ha⟩ := joined_smooth_representative_general k hk hA u v c hm heq
  have hw := seamDomain_weak_gluing hA u v c hm
  have he := Weq.smooth_representative_classical_equation hw heq hF ha
    (Complex.ofRealCLM.continuous.comp (contDiff_potV hk).continuous).continuousOn
  exact ⟨F, hF, ha, fun z hz => add_eq_zero_iff_eq_neg.mpr (he z hz)⟩

end KsIndex.Trace
namespace KsIndex.PaperSlitTransport
open KsIndex.Trace KsIndex.PaperSlitAdapter KsIndex.Surface

theorem pair_radical_seam_classical_representative {α : ℝ} {j : ℕ}
    (u : paperSlitCharacterDomain α j) (hrad : ∀ w, Bpair u w = 0) :
    ∃ F : ℂ → ℂ,
      ContDiffOn ℝ (⊤ : ℕ∞) F
        (seamDomain (boundaryArc 3 0) (isOpen_boundaryArc 3 0) : Set ℂ) ∧
      joinedDiskValue u.val.1 u.val.2 (Complex.exp ((2 * Real.pi * α) * Complex.I))
        =ᵐ[volume.restrict (seamDomain (boundaryArc 3 0) (isOpen_boundaryArc 3 0) : Set ℂ)] F ∧
      ∀ z ∈ seamDomain (boundaryArc 3 0) (isOpen_boundaryArc 3 0),
        laplacian F z + (potV 3 z : ℂ) * F z = 0 := by
  have hm := (mem_slitTraceDomain 3 _ u.val).mp u.property.1
  exact joined_classical_representative_general 3 (by decide)
    (isOpen_boundaryArc 3 0) u.val.1 u.val.2 _ hm.2
    (pair_radical_seam_weak_equation u hrad)

theorem pair_radical_seam_one_classical_representative {α : ℝ} {j : ℕ}
    (u : paperSlitCharacterDomain α j) (hrad : ∀ w, Bpair u w = 0) :
    ∃ F : ℂ → ℂ,
      ContDiffOn ℝ (⊤ : ℕ∞) F
        (seamDomain (boundaryArc 3 1) (isOpen_boundaryArc 3 1) : Set ℂ) ∧
      joinedDiskValue u.val.1 u.val.2 1
        =ᵐ[volume.restrict (seamDomain (boundaryArc 3 1) (isOpen_boundaryArc 3 1) : Set ℂ)] F ∧
      ∀ z ∈ seamDomain (boundaryArc 3 1) (isOpen_boundaryArc 3 1),
        laplacian F z + (potV 3 z : ℂ) * F z = 0 := by
  have hm := (mem_slitTraceDomain 3 _ u.val).mp u.property.1
  exact joined_classical_representative_general 3 (by decide)
    (isOpen_boundaryArc 3 1) u.val.1 u.val.2 1
    (by simpa only [one_smul] using hm.1)
    (pair_radical_seam_one_weak_equation u hrad)

end KsIndex.PaperSlitTransport
