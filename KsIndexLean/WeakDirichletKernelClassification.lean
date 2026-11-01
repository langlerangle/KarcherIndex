module

public import KsIndexLean.PuncturedModeLinearity
public import KsIndexLean.JacobiComparisonKernels

@[expose] public section


noncomputable section
open Set MeasureTheory
namespace KsIndex.Trace
open KsIndex.WeakH1 KsIndex.Radial

/-- Any nonzero full Dirichlet weak solution spans all full Dirichlet solutions. -/
lemma weak_dirichlet_eq_smul_of_nonzero {k : ℕ} (hk : 2 ≤ k)
    (u v : ComplexH1)
    (hu : ∀ w : ComplexH1, w ∈ zeroTraceDomain Set.univ →
      weakJacobi (surfacePotential k) u w = 0)
    (hv : ∀ w : ComplexH1, w ∈ zeroTraceDomain Set.univ →
      weakJacobi (surfacePotential k) v w = 0)
    (htu : diskTraceCLM u = 0) (htv : diskTraceCLM v = 0) (hv0 : v ≠ 0) :
    ∃ c : ℂ, u = c • v := by
  obtain ⟨cu, hcu⟩ := puncturedDiskMode_eq_const_mul_uRad_closed hk u 0 hu
  obtain ⟨cv, hcv⟩ := puncturedDiskMode_eq_const_mul_uRad_closed hk v 0 hv
  have hcv0 : cv ≠ 0 := by
    intro he
    apply hv0
    apply complexH1_eq_of_punctured_modes
    intro n r hr
    rw [puncturedDiskMode_zero n hr]
    by_cases hn : n = 0
    · subst n
      rw [hcv r hr, he, zero_mul]
    · exact weak_dirichlet_nonzero_mode_vanishes hk v n hn hv htv r hr
  refine ⟨cu / cv, complexH1_eq_of_punctured_modes u ((cu / cv) • v) ?_⟩
  intro n r hr
  rw [puncturedDiskMode_smul _ _ _ hr]
  by_cases hn : n = 0
  · subst n
    rw [hcu r hr, hcv r hr]
    field_simp
  · rw [weak_dirichlet_nonzero_mode_vanishes hk u n hn hu htu r hr,
      weak_dirichlet_nonzero_mode_vanishes hk v n hn hv htv r hr, mul_zero]

/-- The actual k=3 full Dirichlet weak kernel is spanned by the vertical field. -/
lemma fullDirichlet_kernel_eq_smul_vertical (u : zeroTraceDomain Set.univ)
    (hu : ∀ v : zeroTraceDomain Set.univ,
      weakJacobi (surfacePotential 3) u v = 0) :
    ∃ c : ℂ, (u : ComplexH1) = c • verticalThreeH1 :=
  weak_dirichlet_eq_smul_of_nonzero (by decide : 2 ≤ 3) u verticalThreeH1
    (fun w hw => hu ⟨w, hw⟩)
    (fun w hw => verticalThree_dirichlet_weak ⟨w, hw⟩)
    ((mem_fullZeroTrace_iff u).mp u.property) verticalThreeH1_trace verticalThreeH1_ne_zero

lemma fullDirichlet_kernel_iff_smul_vertical (u : zeroTraceDomain Set.univ) :
    (∀ v : zeroTraceDomain Set.univ, weakJacobi (surfacePotential 3) u v = 0) ↔
      ∃ c : ℂ, (u : ComplexH1) = c • verticalThreeH1 := by
  constructor
  · exact fullDirichlet_kernel_eq_smul_vertical u
  · rintro ⟨c, hc⟩ v
    rw [hc, weakJacobi_smul_left, verticalThree_dirichlet_weak v, mul_zero]

end KsIndex.Trace
