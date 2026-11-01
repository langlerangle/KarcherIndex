module

public import KsIndexLean.KarcherQuotientJacobiOperator
public import KsIndexLean.SigmaLaplacian

@[expose] public section


/-! Coordinate Jacobi operators and their conformal normalization. -/
noncomputable section
open Set Topology
open scoped ContDiff
namespace KsIndex.KarcherData

/-- The geometric Jacobi expression in an EW disk coordinate. -/
def diskJacobi (k : ℕ) (f : ℂ → ℂ) (z : ℂ) : ℂ :=
  Surface.laplacianG k f z + (Surface.absA k z : ℂ)^2 * f z

lemma diskJacobi_eq_flat {k : ℕ} (hk : 2 ≤ k) {z : ℂ}
    (hz : z ∉ Surface.punctures k) (f : ℂ → ℂ) :
    diskJacobi k f z = ((Surface.rho k z : ℂ)^2)⁻¹ *
      (Surface.laplacian f z + (Surface.potV k z : ℂ) * f z) := by
  have hr : (Surface.rho k z : ℂ) ≠ 0 := by
    have hn : Surface.rho k z ≠ 0 := by
      intro he
      simpa [he] using rho_sq_pos hk hz
    exact_mod_cast hn
  have hV := congrArg (fun x : ℝ => (x : ℂ)) (JacobiFields.absA_sq_mul_rho_sq hk hz)
  push_cast at hV
  unfold diskJacobi Surface.laplacianG
  push_cast
  field_simp
  linear_combination hV * f z

lemma diskJacobi_eq_zero_iff_flat {k : ℕ} (hk : 2 ≤ k) {z : ℂ}
    (hz : z ∉ Surface.punctures k) (f : ℂ → ℂ) :
    diskJacobi k f z = 0 ↔
      Surface.laplacian f z + (Surface.potV k z : ℂ) * f z = 0 := by
  rw [diskJacobi_eq_flat hk hz]
  have hr : (Surface.rho k z : ℂ) ≠ 0 := by
    have hn : Surface.rho k z ≠ 0 := by
      intro he
      simpa [he] using rho_sq_pos hk hz
    exact_mod_cast hn
  exact mul_eq_zero_iff_left (inv_ne_zero (pow_ne_zero _ hr))

lemma diskJacobi_comp_sigma {k : ℕ} (hk : 2 ≤ k) {z : ℂ} (hz : z ≠ 0)
    (hp : z ∉ Surface.punctures k) {f : ℂ → ℂ}
    (hf : ContDiffAt ℝ 2 f (Bracket.σ z)) :
    diskJacobi k (f ∘ Bracket.σ) z = diskJacobi k f (Bracket.σ z) := by
  unfold diskJacobi Surface.laplacianG
  rw [EndChart.laplacian_comp_sigma hz hf, rho_sigma hk hz hp, absA_sigma hk hz hp]
  simp only [Function.comp_apply]
  push_cast
  have hn : (‖z‖ : ℂ) ≠ 0 := by exact_mod_cast (norm_ne_zero_iff.mpr hz)
  field_simp

lemma laplacian_comp_conj (f : ℂ → ℂ) (z : ℂ) :
    Surface.laplacian (f ∘ (starRingEnd ℂ)) z =
      Surface.laplacian f ((starRingEnd ℂ) z) := by
  have hd (g : ℂ → ℂ) (w : ℂ) :
      fderiv ℝ (g ∘ (starRingEnd ℂ)) w =
        (fderiv ℝ g ((starRingEnd ℂ) w)).comp Complex.conjCLE.toContinuousLinearMap :=
    Complex.conjCLE.comp_right_fderiv
  have h1 : (fun w => fderiv ℝ (f ∘ (starRingEnd ℂ)) w 1) =
      (fun w => fderiv ℝ f w 1) ∘ (starRingEnd ℂ) := by
    funext w
    rw [hd]
    simp
  have hI : (fun w => fderiv ℝ (f ∘ (starRingEnd ℂ)) w Complex.I) =
      -((fun w => fderiv ℝ f w Complex.I) ∘ (starRingEnd ℂ)) := by
    funext w
    rw [hd]
    simp
  unfold Surface.laplacian
  rw [h1, hI, fderiv_neg, hd, hd]
  simp

lemma diskJacobi_comp_conj (k : ℕ) (f : ℂ → ℂ) (z : ℂ) :
    diskJacobi k (f ∘ (starRingEnd ℂ)) z = diskJacobi k f ((starRingEnd ℂ) z) := by
  simp only [diskJacobi, Surface.laplacianG, laplacian_comp_conj,
    rho_conj, absA_conj, Function.comp_apply]

end KsIndex.KarcherData
