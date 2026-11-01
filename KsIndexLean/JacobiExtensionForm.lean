module

public import KsIndexLean.JacobiExtensionCharacter
public import KsIndexLean.DtnBridge

@[expose] public section


noncomputable section
open Set MeasureTheory
namespace KsIndex.Trace
open KsIndex.WeakH1 KsIndex.DtNCircle KsIndex.CircleSobolev KsIndex.DtnBridge

/-- Full Green pairing of the convergent Jacobi extension against any weak H1 test.
No L2 representative of its generally distributional normal derivative is assumed. -/
lemma jacobiExtensionH1_weak_pairing {k : ℕ} (hk : 2 ≤ k)
    (f : Space (1 / 2 : ℝ)) (v : ComplexH1) :
    weakJacobi (surfacePotential k) (jacobiExtensionH1 hk f) v =
      (2 * Real.pi : ℂ) * ∑' n : NZ, (dtnSymbol k n : ℂ) *
        (starRingEnd ℂ) (coeff (1 / 2 : ℝ) f n) * circleFourierCoeff (diskTraceCLM v) n := by
  let L : ComplexH1 →L⋆[ℂ] ℂ :=
    { toFun := fun u => weakJacobi (surfacePotential k) u v
      map_add' := fun u w => weakJacobi_add_left _ u w v
      map_smul' := fun c u => weakJacobi_smul_left _ c u v
      cont := by
        simpa only [Function.comp_def, weakJacobi_conj] using
          Complex.continuous_conj.comp (continuous_weakJacobi_fixed_left (surfacePotential k) v) }
  have h := L.map_tsum (jacobiExtension_summable hk f)
  change weakJacobi (surfacePotential k) (jacobiExtensionH1 hk f) v =
    ∑' n : NZ, weakJacobi (surfacePotential k)
      (coeff (1 / 2 : ℝ) f n • normalizedJacobiMode hk n) v at h
  rw [h, ← tsum_mul_left]
  apply tsum_congr
  intro n
  rw [weakJacobi_smul_left, normalizedJacobiMode_weak_green,
    inner_smul_left, fourierTestLp_inner_unscaled, Complex.conj_ofReal]
  push_cast
  ring

/-- Exact disk/circle sesquilinear identity on the full mean-zero half-order space. -/
lemma jacobiExtensionCLM_form {k : ℕ} (hk : 2 ≤ k)
    (f g : dotted (1 / 2 : ℝ)) :
    weakJacobi (surfacePotential k) (jacobiExtensionCLM hk f) (jacobiExtensionCLM hk g) =
      (2 * Real.pi : ℂ) * faithfulDtnB k f g := by
  change weakJacobi (surfacePotential k) (jacobiExtensionH1 hk f) (jacobiExtensionH1 hk g) = _
  rw [jacobiExtensionH1_weak_pairing, faithfulDtnB]
  congr 1
  apply tsum_congr
  intro n
  rw [jacobiExtensionH1_trace_coefficient, ite_eq_right n.property]

/-- The same identity against the corpus DtN operator and half-order duality. -/
lemma jacobiExtensionCLM_form_duality {k : ℕ} (hk : 2 ≤ k)
    (f g : dotted (1 / 2 : ℝ)) :
    weakJacobi (surfacePotential k) (jacobiExtensionCLM hk f) (jacobiExtensionCLM hk g) =
      duality (1 / 2 : ℝ) (dottedDtnCLM k f).val g.val := by
  rw [jacobiExtensionCLM_form, duality_dottedDtnCLM]

/-- Honest sesquilinear block identity, before restricting to any character or mixed domain. -/
lemma jacobiExtensionCLM_block_form {k : ℕ} (hk : 2 ≤ k)
    (f g : dotted (1 / 2 : ℝ)) (w v : ComplexH1)
    (hw : w ∈ zeroTraceDomain Set.univ) (hv : v ∈ zeroTraceDomain Set.univ) :
    weakJacobi (surfacePotential k) (jacobiExtensionCLM hk f + w) (jacobiExtensionCLM hk g + v) =
      (2 * Real.pi : ℂ) * faithfulDtnB k f g + weakJacobi (surfacePotential k) w v := by
  have hc : weakJacobi (surfacePotential k) w (jacobiExtensionCLM hk g) = 0 := by
    rw [← weakJacobi_conj, jacobiExtensionCLM_weak_zeroTrace hk g w hw, map_zero]
  rw [weakJacobi_add_left, weakJacobi_add_right, weakJacobi_add_right,
    jacobiExtensionCLM_form, jacobiExtensionCLM_weak_zeroTrace hk f v hv, hc, add_zero, zero_add]

end KsIndex.Trace
