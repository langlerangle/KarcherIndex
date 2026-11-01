module

public import KsIndexLean.PaperSlitInteriorSmooth
public import KsIndexLean.WeakEquationLinear

@[expose] public section


noncomputable section
open Set MeasureTheory
namespace KsIndex.Weq
open KsIndex.WeakH1

lemma disk_complex_weak_equation (u : ComplexH1)
    (hr : PunctureRemoval.IsWeakSolOn (Surface.potV 3) disk (rePart u))
    (hi : PunctureRemoval.IsWeakSolOn (Surface.potV 3) disk (imPart u)) :
    InteriorWeakEquation disk (dxLp u) (dyLp u)
      (fun z => (Surface.potV 3 z : ℂ) * valueCLM u z) :=
  general_disk_complex_weak_equation (by decide) u hr hi

lemma disk_smooth_representative_classical (u : ComplexH1)
    (hr : PunctureRemoval.IsWeakSolOn (Surface.potV 3) disk (rePart u))
    (hi : PunctureRemoval.IsWeakSolOn (Surface.potV 3) disk (imPart u))
    {F : ℂ → ℂ} (hF : ContDiffOn ℝ (⊤ : ℕ∞) F (disk : Set ℂ))
    (ha : valueCLM u =ᵐ[volume.restrict (disk : Set ℂ)] F) :
    ∀ z ∈ (disk : Set ℂ), Surface.laplacian F z + (Surface.potV 3 z : ℂ) * F z = 0 :=
  general_disk_smooth_representative_classical (by decide) u hr hi hF ha

end KsIndex.Weq
namespace KsIndex.PaperSlitTransport
open KsIndex.Trace KsIndex.WeakH1 KsIndex.PaperSlitAdapter

/-- Both disk representatives of the actual radical satisfy the pointwise
flat-chart Jacobi equation on the whole open disk. -/
theorem pair_radical_disk_classical_representatives {α : ℝ} {j : ℕ}
    (u : paperSlitCharacterDomain α j) (hrad : ∀ w, Bpair u w = 0) :
    ∃ f g : ℂ → ℂ,
      ContDiffOn ℝ (⊤ : ℕ∞) f (disk : Set ℂ) ∧
      ContDiffOn ℝ (⊤ : ℕ∞) g (disk : Set ℂ) ∧
      valueCLM u.val.1 =ᵐ[volume.restrict (disk : Set ℂ)] f ∧
      valueCLM u.val.2 =ᵐ[volume.restrict (disk : Set ℂ)] g ∧
      (∀ z ∈ (disk : Set ℂ), Surface.laplacian f z + (Surface.potV 3 z : ℂ) * f z = 0) ∧
      (∀ z ∈ (disk : Set ℂ), Surface.laplacian g z + (Surface.potV 3 z : ℂ) * g z = 0) := by
  obtain ⟨f, g, hf, hg, ha, hb⟩ := pair_radical_smooth_representatives u hrad
  refine ⟨f, g, hf, hg, ha, hb, ?_, ?_⟩
  · exact Weq.disk_smooth_representative_classical u.val.1
      (fun φ hs hc ht => (pair_radical_D1_fst u hrad φ hs hc ht).1)
      (fun φ hs hc ht => (pair_radical_D1_fst u hrad φ hs hc ht).2) hf ha
  · exact Weq.disk_smooth_representative_classical u.val.2
      (fun φ hs hc ht => (pair_radical_D1_snd u hrad φ hs hc ht).1)
      (fun φ hs hc ht => (pair_radical_D1_snd u hrad φ hs hc ht).2) hg hb

end KsIndex.PaperSlitTransport
