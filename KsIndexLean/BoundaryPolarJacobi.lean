module

public import KsIndexLean.BoundaryPolarDirichlet
public import KsIndexLean.WeakH1Integration
public import KsIndexLean.RadialMode

@[expose] public section


noncomputable section
open Set MeasureTheory
open scoped ContDiff
namespace KsIndex.Trace
open KsIndex.WeakH1

lemma potential_boundaryPolarTest_modes {a c : ℝ}
    (ha : 0 < a) (hab : a < 1)
    {χ : ℝ → ℝ} (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ)
    (hs : tsupport χ ⊆ Ioo a c) (n : ℤ) (u : ComplexH1)
    (V : BoundedRealPotential) {W : ℝ → ℝ} (hW : ContDiff ℝ ∞ W)
    (hV : ∀ z ∈ (disk : Set ℂ), V.V z = W ‖z‖) :
    potential V u (compactPolarTestH1 ha hχ hs n) =
      ∫ r in Ioo a 1, (r * (χ r * W r) : ℝ) •
        (((2 * Real.pi : ℝ) : ℂ) * (starRingEnd ℂ) (interiorDiskMode hab u n r)) := by
  have hp : ContDiff ℝ ∞ (fun r => χ r * W r) := hχ.mul hW
  have hpc : HasCompactSupport (fun r => χ r * W r) := hc.mul_right
  have hps : tsupport (fun r => χ r * W r) ⊆ Ioo a c := tsupport_mul_subset_left.trans hs
  rw [potential_integral]
  have he : (∫ z in (disk : Set ℂ), (V.V z : ℂ) * (starRingEnd ℂ) (valueCLM u z) *
      valueCLM (compactPolarTestH1 ha hχ hs n) z) =
      ∫ z in (disk : Set ℂ), compactPolarTest (fun r => χ r * W r) n z *
        (starRingEnd ℂ) (valueCLM u z) := by
    apply integral_congr_ae
    filter_upwards [globalSmoothH1_value (compactPolarTest χ n)
      (compactPolarTest_smooth ha hχ hs n), ae_restrict_mem disk.isOpen.measurableSet] with z hz hzD
    change (V.V z : ℂ) * (starRingEnd ℂ) (valueCLM u z) *
      valueCLM (globalSmoothH1 (compactPolarTest χ n) (compactPolarTest_smooth ha hχ hs n)) z = _
    rw [hz, hV z hzD]
    simp only [compactPolarTest, Complex.ofReal_mul]
    ring
  rw [he, integral_disk_boundaryPolarTest_mul hps n]
  exact integral_annulus_boundaryPolarTest_value ha hab le_rfl hp hpc hps n u

/-- The full weak Jacobi pairing, before imposing the weak kernel equation. -/
lemma weakJacobi_boundaryPolarTest_modes {a c : ℝ}
    (ha : 0 < a) (hab : a < 1)
    {χ : ℝ → ℝ} (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ)
    (hs : tsupport χ ⊆ Ioo a c) (n : ℤ) (u : ComplexH1)
    (V : BoundedRealPotential) {W : ℝ → ℝ} (hW : ContDiff ℝ ∞ W)
    (hV : ∀ z ∈ (disk : Set ℂ), V.V z = W ‖z‖) :
    weakJacobi V u (compactPolarTestH1 ha hχ hs n) =
      ((∫ r in Ioo a 1, (r * deriv χ r : ℝ) •
        (((2 * Real.pi : ℝ) : ℂ) * (starRingEnd ℂ) (interiorDiskRadialMode a 1 u n r))) +
      ∫ r in Ioo a 1, (χ r / r : ℝ) •
        (((2 * Real.pi : ℝ) : ℂ) * (n : ℂ)^2 *
          (starRingEnd ℂ) (interiorDiskMode hab u n r))) -
      ∫ r in Ioo a 1, (r * (χ r * W r) : ℝ) •
        (((2 * Real.pi : ℝ) : ℂ) * (starRingEnd ℂ) (interiorDiskMode hab u n r)) := by
  rw [weakJacobi, weakDirichlet_boundaryPolarTest_modes ha hab hχ hc hs n u,
    potential_boundaryPolarTest_modes ha hab hχ hc hs n u V hW hV]


end KsIndex.Trace
