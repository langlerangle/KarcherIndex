module

public import KsIndexLean.WeakH1Integration
public import KsIndexLean.SphericalMassNorm

@[expose] public section


noncomputable section
open Set MeasureTheory
namespace KsIndex.WeakH1

/-- Potential control in the bulk L2 norm, needed for a mass shift. -/
lemma norm_potential_le_bulk (V : BoundedRealPotential) (u v : ComplexH1) :
    ‖potential V u v‖ ≤ V.C * ‖valueCLM u‖ * ‖valueCLM v‖ := by
  calc
    _ ≤ ‖valueCLM u‖ * ‖weightedLp V (valueCLM v)‖ := norm_inner_le_norm _ _
    _ ≤ ‖valueCLM u‖ * (V.C * ‖valueCLM v‖) :=
      mul_le_mul_of_nonneg_left (norm_weightedLp_le V _) (norm_nonneg _)
    _ = _ := by ring

/-- Any mass dominating disk L2 makes the shifted Jacobi form coercive in H1. -/
theorem weakJacobi_shift_coercive (V : BoundedRealPotential) (u : ComplexH1)
    {M : ℝ} (hM : ‖valueCLM u‖ ^ 2 ≤ M) :
    ‖u‖ ^ 2 ≤ (weakJacobi V u u).re + (V.C + 1) * M := by
  have hp : (potential V u u).re ≤ V.C * ‖valueCLM u‖ ^ 2 := by
    have he := (Complex.re_le_norm (potential V u u)).trans (norm_potential_le_bulk V u u)
    nlinarith
  have hd : (dirichlet u u).re = ‖dxLp u‖ ^ 2 + ‖dyLp u‖ ^ 2 := by
    change (inner ℂ (dxLp u) (dxLp u) + inner ℂ (dyLp u) (dyLp u)).re = _
    simp only [Complex.add_re, inner_self_eq_norm_sq_to_K]
    change ((‖dxLp u‖ : ℂ) ^ 2).re + ((‖dyLp u‖ : ℂ) ^ 2).re = _
    simp only [← Complex.ofReal_pow, Complex.ofReal_re]
  have hs := mul_le_mul_of_nonneg_left hM (show 0 ≤ V.C + 1 by linarith [V.nonneg])
  rw [coordinate_graph_norm_sq, weakJacobi, Complex.sub_re, hd]
  nlinarith

/-- Summed-copy form coercivity; no boundary, phase, or character restriction. -/
theorem sum_weakJacobi_shift_coercive {ι : Type*} [Fintype ι]
    (V : BoundedRealPotential) (u : ι → ComplexH1) {M : ℝ}
    (hM : (∑ i, ‖valueCLM (u i)‖ ^ 2) ≤ M) :
    (∑ i, ‖u i‖ ^ 2) ≤ (∑ i, weakJacobi V (u i) (u i)).re + (V.C + 1) * M := by
  have hs := Finset.sum_le_sum (s := Finset.univ)
    (fun i _ => weakJacobi_shift_coercive V (u i) (M := ‖valueCLM (u i)‖ ^ 2) le_rfl)
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum, Complex.re_sum] at hs ⊢
  have hm := mul_le_mul_of_nonneg_left hM (show 0 ≤ V.C + 1 by linarith [V.nonneg])
  linarith

end KsIndex.WeakH1

namespace KsIndex.Spherical
open KsIndex.WeakH1

/-- Coercivity with the actual canonical spherical mass, using its lower bound. -/
theorem sphereJoinedJacobi_shift_coercive (V : BoundedRealPotential) (u v : ComplexH1) :
    ‖u‖ ^ 2 + ‖v‖ ^ 2 ≤ (weakJacobi V u u + weakJacobi V v v).re + (V.C + 1) *
      (∫⁻ p, ENNReal.ofReal (‖sphereJoinedValue u v p‖ ^ 2)
        ∂(volume : Measure Ambient).toSphere).toReal := by
  have hu := weakJacobi_shift_coercive V u (M := ‖valueCLM u‖ ^ 2) le_rfl
  have hv := weakJacobi_shift_coercive V v (M := ‖valueCLM v‖ ^ 2) le_rfl
  have hm := mul_le_mul_of_nonneg_left (sphereJoinedValue_mass_real_comparison u v).1
    (show 0 ≤ V.C + 1 by linarith [V.nonneg])
  simp only [Complex.add_re]
  nlinarith

/-- An explicit shift for the paper's actual surface potential. -/
theorem surfaceJoinedJacobi_shift_coercive (k : ℕ) (u v : ComplexH1) :
    ‖u‖ ^ 2 + ‖v‖ ^ 2 ≤
      (weakJacobi (surfacePotential k) u u + weakJacobi (surfacePotential k) v v).re +
      (8 * ((k : ℝ) - 1) ^ 2 + 1) *
      (∫⁻ p, ENNReal.ofReal (‖sphereJoinedValue u v p‖ ^ 2)
        ∂(volume : Measure Ambient).toSphere).toReal :=
  sphereJoinedJacobi_shift_coercive (surfacePotential k) u v

end KsIndex.Spherical
