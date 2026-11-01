module

public import KsIndexLean.CompactPolarWeights
public import KsIndexLean.WeakH1Integration
public import KsIndexLean.RadialMode

@[expose] public section


noncomputable section
open Set MeasureTheory
open scoped ContDiff
namespace KsIndex.Trace
open KsIndex.WeakH1

lemma potential_compactPolarTest_modes {a b : ℝ}
    (ha : 0 < a) (hab : a < b) (hb : b ≤ 1)
    {χ : ℝ → ℝ} (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ)
    (hs : tsupport χ ⊆ Ioo a b) (n : ℤ) (u : ComplexH1)
    (V : BoundedRealPotential) {W : ℝ → ℝ} (hW : ContDiff ℝ ∞ W)
    (hV : ∀ z ∈ (disk : Set ℂ), V.V z = W ‖z‖) :
    potential V u (compactPolarTestH1 ha hχ hs n) =
      ∫ r in Ioo a b, (r * (χ r * W r) : ℝ) •
        (((2 * Real.pi : ℝ) : ℂ) * (starRingEnd ℂ) (interiorDiskMode hab u n r)) := by
  have hp : ContDiff ℝ ∞ (fun r => χ r * W r) := hχ.mul hW
  have hpc : HasCompactSupport (fun r => χ r * W r) := hc.mul_right
  have hps : tsupport (fun r => χ r * W r) ⊆ Ioo a b := tsupport_mul_subset_left.trans hs
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
  rw [he, ← integral_compactPolarTest_value ha hab hb hp hpc hps n u]
  apply setIntegral_eq_integral_of_forall_compl_eq_zero
  intro z hz
  have hn : z ∉ tsupport (compactPolarTest (fun r => χ r * W r) n) :=
    fun h => hz (interiorAnnulus_subset_disk hb (compactPolarTest_annular_support hps n h))
  rw [image_eq_zero_of_notMem_tsupport hn, zero_mul]

/-- The full weak Jacobi pairing, before imposing the weak kernel equation. -/
lemma weakJacobi_compactPolarTest_modes {a b : ℝ}
    (ha : 0 < a) (hab : a < b) (hb : b ≤ 1)
    {χ : ℝ → ℝ} (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ)
    (hs : tsupport χ ⊆ Ioo a b) (n : ℤ) (u : ComplexH1)
    (V : BoundedRealPotential) {W : ℝ → ℝ} (hW : ContDiff ℝ ∞ W)
    (hV : ∀ z ∈ (disk : Set ℂ), V.V z = W ‖z‖) :
    weakJacobi V u (compactPolarTestH1 ha hχ hs n) =
      ((∫ r in Ioo a b, (r * deriv χ r : ℝ) •
        (((2 * Real.pi : ℝ) : ℂ) * (starRingEnd ℂ) (interiorDiskRadialMode a b u n r))) +
      ∫ r in Ioo a b, (χ r / r : ℝ) •
        (((2 * Real.pi : ℝ) : ℂ) * (n : ℂ)^2 *
          (starRingEnd ℂ) (interiorDiskMode hab u n r))) -
      ∫ r in Ioo a b, (r * (χ r * W r) : ℝ) •
        (((2 * Real.pi : ℝ) : ℂ) * (starRingEnd ℂ) (interiorDiskMode hab u n r)) := by
  rw [weakJacobi, weakDirichlet_compactPolarTest_modes ha hab hb hχ hc hs n u,
    potential_compactPolarTest_modes ha hab hb hχ hc hs n u V hW hV]

lemma contDiff_Vrad (k : ℕ) : ContDiff ℝ ∞ (KsIndex.Radial.Vrad k) := by
  unfold KsIndex.Radial.Vrad
  exact ContDiff.div (by fun_prop) (by fun_prop)
    (fun r => pow_ne_zero 2 (KsIndex.Radial.denom_pos k r).ne')

/-- The explicit paper potential satisfies the radial reduction without an imported
radiality or smoothness hypothesis. -/
lemma surfaceJacobi_compactPolarTest_modes {a b : ℝ}
    (ha : 0 < a) (hab : a < b) (hb : b ≤ 1)
    {χ : ℝ → ℝ} (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ)
    (hs : tsupport χ ⊆ Ioo a b) (k : ℕ) (n : ℤ) (u : ComplexH1) :
    weakJacobi (surfacePotential k) u (compactPolarTestH1 ha hχ hs n) =
      ((∫ r in Ioo a b, (r * deriv χ r : ℝ) •
        (((2 * Real.pi : ℝ) : ℂ) * (starRingEnd ℂ) (interiorDiskRadialMode a b u n r))) +
      ∫ r in Ioo a b, (χ r / r : ℝ) •
        (((2 * Real.pi : ℝ) : ℂ) * (n : ℂ)^2 *
          (starRingEnd ℂ) (interiorDiskMode hab u n r))) -
      ∫ r in Ioo a b, (r * (χ r * KsIndex.Radial.Vrad k r) : ℝ) •
        (((2 * Real.pi : ℝ) : ℂ) * (starRingEnd ℂ) (interiorDiskMode hab u n r)) := by
  apply weakJacobi_compactPolarTest_modes ha hab hb hχ hc hs n u
    (surfacePotential k) (contDiff_Vrad k)
  intro z _
  exact KsIndex.Radial.potV_eq_Vrad k z

/-- Every actual weak solution against zero-boundary tests satisfies the Fourier
mode integral equation on each annulus. Regularity at the centre is not assumed. -/
lemma surfaceJacobi_weak_mode_equation {a b : ℝ}
    (ha : 0 < a) (hab : a < b) (hb : b ≤ 1)
    {χ : ℝ → ℝ} (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ)
    (hs : tsupport χ ⊆ Ioo a b) (k : ℕ) (n : ℤ) (u : ComplexH1)
    (hu : ∀ v : ComplexH1, v ∈ zeroTraceDomain Set.univ →
      weakJacobi (surfacePotential k) u v = 0) :
      ((∫ r in Ioo a b, (r * deriv χ r : ℝ) •
        (((2 * Real.pi : ℝ) : ℂ) * (starRingEnd ℂ) (interiorDiskRadialMode a b u n r))) +
      ∫ r in Ioo a b, (χ r / r : ℝ) •
        (((2 * Real.pi : ℝ) : ℂ) * (n : ℂ)^2 *
          (starRingEnd ℂ) (interiorDiskMode hab u n r))) -
      ∫ r in Ioo a b, (r * (χ r * KsIndex.Radial.Vrad k r) : ℝ) •
        (((2 * Real.pi : ℝ) : ℂ) * (starRingEnd ℂ) (interiorDiskMode hab u n r)) = 0 := by
  rw [← surfaceJacobi_compactPolarTest_modes ha hab hb hχ hc hs k n u]
  exact hu _ (compactPolarTestH1_zeroTrace ha hb hχ hs n Set.univ)

end KsIndex.Trace
