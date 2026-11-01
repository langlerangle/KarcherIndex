module

public import Mathlib.Analysis.Calculus.Deriv.Star
public import KsIndexLean.VerticalWeakGreen
public import KsIndexLean.SlitHorizontalExclusion

@[expose] public section


noncomputable section
open Set MeasureTheory
open scoped ContDiff
namespace KsIndex.Trace
open KsIndex.WeakH1 KsIndex.Surface KsIndex.JacobiFields

/-- A globally smooth Jacobi solution with zero normal derivative annihilates
all unrestricted H1 tests. Density is used only on the test side. -/
lemma smooth_neumann_weak (V : BoundedRealPotential) (u : ℂ → ℂ)
    (hu : ContDiff ℝ ∞ u)
    (hjac : ∀ w ∈ (WeakH1.disk : Set ℂ), laplacian u w + (V.V w : ℂ) * u w = 0)
    (hn : ∀ w : Circle₁, fderiv ℝ u w w = 0) (v : ComplexH1) :
    weakJacobi V (globalSmoothH1 u hu) v = 0 := by
  have hc : Continuous (fun v : mixedCharacterDomain 1 0 true true =>
      weakJacobi V (globalSmoothH1 u hu) v) :=
    (continuous_weakJacobi_fixed_left V (globalSmoothH1 u hu)).comp continuous_subtype_val
  have he := (naturalCharacterToMixed_denseRange (k := 1) (by decide) 0 true true).equalizer
    hc (continuous_const : Continuous (fun _ : mixedCharacterDomain 1 0 true true => (0 : ℂ))) (by
      funext f
      let ff : KsIndex.SingleDisk.NatCc 1 true true := ⟨f.val, f.property.1⟩
      obtain ⟨G, hG, hv, hx, hy, ht⟩ := naturalCoreH1_C1_representative (by decide : 1 ≤ 1) ff
      have h := weakJacobi_C1_test_green V u G hu hG (naturalCoreH1 (by decide) ff) hv hx hy hjac
      change weakJacobi V (globalSmoothH1 u hu) (naturalCoreH1 (by decide) ff) = 0
      rw [h]
      have hz : (fun w : Circle₁ => (starRingEnd ℂ) (fderiv ℝ u w w) * G w) = 0 := by
        funext w
        rw [hn w, map_zero, zero_mul]
        rfl
      rw [hz]
      exact integral_zero Circle₁ ℂ)
  exact congrFun he ⟨v, mem_trivial_NN_sector v⟩

lemma horizontal_combination_jacobi (k : ℕ) (hk : 2 ≤ k) (c : ℂ) (w : ℂ) :
    laplacian (fun z => nu1 k z + c * nu2 k z) w +
      (KsIndex.Surface.potV k w : ℂ) * (nu1 k w + c * nu2 k w) = 0 := by
  have h1 := (nu1_contDiff k hk).contDiffAt (x := w)
  have h2 := (nu2_contDiff k hk).contDiffAt (x := w)
  have hc : ContDiffAt ℝ ∞ (c • nu2 k) w := contDiffAt_const.smul h2
  change laplacian (nu1 k + c • nu2 k) w + _ = 0
  rw [laplacian_add h1 hc, laplacian_smul c h2]
  linear_combination (jacobi_nu1 k hk w) + c * (jacobi_nu2 k hk w)

lemma horizontalThree_combination_jacobi (c : ℂ) (w : ℂ) :
    laplacian (fun z => nu1 3 z + c * nu2 3 z) w +
      (KsIndex.Surface.potV 3 w : ℂ) * (nu1 3 w + c * nu2 3 w) = 0 := by
  exact horizontal_combination_jacobi 3 (by decide) c w

/-- The complex horizontal field as an actual H1 representative, for general k. -/
def horizontalH1 (k : ℕ) (hk : 2 ≤ k) : ComplexH1 :=
  globalSmoothH1 (fun z => nu1 k z + Complex.I * nu2 k z)
    ((nu1_contDiff k hk).add (contDiff_const.mul (nu2_contDiff k hk)))

lemma horizontalH1_trace (k : ℕ) (hk : 2 ≤ k) :
    (diskTraceCLM (horizontalH1 k hk) : Circle₁ → ℂ) =ᵐ[circleMeasure]
      (fun w => (w : ℂ) ^ (k - 1)) := by
  filter_upwards [globalSmoothH1_trace
    (fun w => nu1 k w + Complex.I * nu2 k w)
    ((nu1_contDiff k hk).add (contDiff_const.mul (nu2_contDiff k hk)))] with w hw
  have hn : ‖(w : ℂ)‖ = 1 := by
    simpa [Metric.mem_sphere, dist_zero_right] using w.property
  change diskTraceCLM (globalSmoothH1 _ _) w = _
  rw [hw, horizontal_formula, hn]
  norm_num

lemma horizontalH1_ne_zero (k : ℕ) (hk : 2 ≤ k) : horizontalH1 k hk ≠ 0 := by
  intro hz
  have ht := horizontalH1_trace k hk
  rw [hz, map_zero] at ht
  haveI : (ae circleMeasure).NeBot := ae_neBot.mpr (by
    intro hm
    have hh := circleMeasure_univ
    rw [hm] at hh
    change (0 : ENNReal) = ENNReal.ofReal (2 * Real.pi) at hh
    have hp : 0 < ENNReal.ofReal (2 * Real.pi) := by positivity
    rw [← hh] at hp
    exact (lt_irrefl 0) hp)
  obtain ⟨w, hw, hzero⟩ := (ht.and (Lp.coeFn_zero ℂ 2 circleMeasure)).exists
  have hn : ‖(w : ℂ)‖ = 1 := by
    simpa [Metric.mem_sphere, dist_zero_right] using w.property
  have hne : (w : ℂ) ^ (k - 1) ≠ 0 := pow_ne_zero _ (by
    intro h; simp [h] at hn)
  exact hne (hw.symm.trans hzero)

lemma horizontal_normal (k : ℕ) (hk : 2 ≤ k) {w : ℂ} (hw : ‖w‖ = 1) :
    fderiv ℝ (fun z => nu1 k z + Complex.I * nu2 k z) w w = 0 :=
  fderiv_radial_of_hasDerivAt _
    (((nu1_contDiff k hk).add (contDiff_const.mul (nu2_contDiff k hk))).differentiable (by simp) w)
    (horizontal_radial_derivative k hw)

/-- The horizontal field annihilates all weak Neumann tests for every k>=2. -/
lemma horizontal_weak_neumann (k : ℕ) (hk : 2 ≤ k) (v : ComplexH1) :
    weakJacobi (surfacePotential k) (horizontalH1 k hk) v = 0 := by
  apply smooth_neumann_weak
  · intro w _
    exact horizontal_combination_jacobi k hk Complex.I w
  · intro w
    exact horizontal_normal k hk (by simpa [Metric.mem_sphere, dist_zero_right] using w.property)

lemma horizontalThree_normal {w : ℂ} (hw : ‖w‖ = 1) :
    fderiv ℝ (fun z => nu1 3 z + Complex.I * nu2 3 z) w w = 0 :=
  fderiv_radial_of_hasDerivAt _
    (((nu1_contDiff 3 (by decide)).add (contDiff_const.mul (nu2_contDiff 3 (by decide)))).differentiable (by simp) w)
    (horizontal_three_radial_derivative hw)

/-- The actual horizontal H1 field satisfies the unrestricted weak Neumann equation. -/
lemma horizontalThree_weak_neumann (v : ComplexH1) :
    weakJacobi (surfacePotential 3) horizontalThreeH1 v = 0 := by
  apply smooth_neumann_weak
  · intro w _
    exact horizontalThree_combination_jacobi Complex.I w
  · intro w
    exact horizontalThree_normal (by simpa [Metric.mem_sphere, dist_zero_right] using w.property)

lemma horizontalThree_conj_formula :
    (fun w => (starRingEnd ℂ) (nu1 3 w + Complex.I * nu2 3 w)) =
      (fun w => nu1 3 w + (-Complex.I) * nu2 3 w) := by
  funext w
  simp only [map_add, map_mul, nu1, nu2, Complex.conj_ofReal, Complex.conj_I]

lemma horizontalThreeConj_normal {w : ℂ} (hw : ‖w‖ = 1) :
    fderiv ℝ (fun z => (starRingEnd ℂ) (nu1 3 z + Complex.I * nu2 3 z)) w w = 0 := by
  apply fderiv_radial_of_hasDerivAt _
    ((Complex.conjCLE.contDiff.comp ((nu1_contDiff 3 (by decide)).add
      (contDiff_const.mul (nu2_contDiff 3 (by decide))))).differentiable (by simp) w)
  convert (horizontal_three_radial_derivative hw).star using 1 <;>
    first | rfl | simp only [star_zero]

/-- The conjugate horizontal field also annihilates every unrestricted H1 test. -/
lemma horizontalThreeConj_weak_neumann (v : ComplexH1) :
    weakJacobi (surfacePotential 3) horizontalThreeConjH1 v = 0 := by
  apply smooth_neumann_weak
  · intro w _
    change laplacian (fun z => (starRingEnd ℂ) (nu1 3 z + Complex.I * nu2 3 z)) w +
      (KsIndex.Surface.potV 3 w : ℂ) *
        (starRingEnd ℂ) (nu1 3 w + Complex.I * nu2 3 w) = 0
    rw [horizontalThree_conj_formula, congrFun horizontalThree_conj_formula w]
    exact horizontalThree_combination_jacobi (-Complex.I) w
  · intro w
    exact horizontalThreeConj_normal (by simpa [Metric.mem_sphere, dist_zero_right] using w.property)

end KsIndex.Trace
