module

public import KsIndexLean.JacobiExtensionTrace

@[expose] public section


noncomputable section
open Set Filter MeasureTheory
open scoped Topology
namespace KsIndex.Trace
open KsIndex.WeakH1 KsIndex.DtNCircle KsIndex.CircleSobolev

lemma half_coeff_finite_weight_le (f : Space (1 / 2 : ℝ)) (s : Finset NZ) :
    (∑ n ∈ s, (1 + |(n.val : ℝ)|) * ‖coeff (1 / 2 : ℝ) f n‖ ^ 2) ≤ ‖f‖ ^ 2 := by
  classical
  have h := lp.sum_rpow_le_norm_rpow (by norm_num : (0 : ℝ) < (2 : ENNReal).toReal)
    f (s.image Subtype.val)
  simp only [ENNReal.toReal_ofNat, Real.rpow_two] at h
  rw [Finset.sum_image (fun a _ b _ hab => Subtype.ext hab)] at h
  have he (n : NZ) : ‖f n‖ ^ 2 = (1 + |(n.val : ℝ)|) * ‖coeff (1 / 2 : ℝ) f n‖ ^ 2 := by
    rw [norm_sq_coordinate, weight_sq]
    norm_num
  simpa only [he] using h

lemma jacobiExtensionH1_norm_sq_le {k : ℕ} (hk : 2 ≤ k) (f : Space (1 / 2 : ℝ)) :
    ‖jacobiExtensionH1 hk f‖ ^ 2 ≤ jacobiModeH1Constant k * ‖f‖ ^ 2 := by
  have hlim := (hasSum_jacobiExtension hk f).norm.pow 2
  apply le_of_tendsto hlim
  filter_upwards [] with s
  exact (finiteJacobiExtension_norm_sq_le hk s _).trans
    (mul_le_mul_of_nonneg_left (half_coeff_finite_weight_le f s) (jacobiModeH1Constant_nonneg k))

lemma jacobiExtensionH1_norm_le {k : ℕ} (hk : 2 ≤ k) (f : Space (1 / 2 : ℝ)) :
    ‖jacobiExtensionH1 hk f‖ ≤ Real.sqrt (jacobiModeH1Constant k) * ‖f‖ := by
  have h := jacobiExtensionH1_norm_sq_le hk f
  have he := Real.sq_sqrt (jacobiModeH1Constant_nonneg k)
  have hp : 0 ≤ Real.sqrt (jacobiModeH1Constant k) * ‖f‖ := by positivity
  nlinarith [sq_nonneg (‖jacobiExtensionH1 hk f‖ - Real.sqrt (jacobiModeH1Constant k) * ‖f‖)]

/-- Bounded Jacobi extension on the paper's full mean-zero half-order space. -/
def jacobiExtensionCLM {k : ℕ} (hk : 2 ≤ k) : dotted (1 / 2 : ℝ) →L[ℂ] ComplexH1 :=
  LinearMap.mkContinuous
    { toFun := fun f => jacobiExtensionH1 hk f.val
      map_add' := fun f g => jacobiExtensionH1_add hk f.val g.val
      map_smul' := fun c f => jacobiExtensionH1_smul hk c f.val }
    (Real.sqrt (jacobiModeH1Constant k)) (fun f => jacobiExtensionH1_norm_le hk f.val)

lemma jacobiExtensionCLM_halfTrace {k : ℕ} (hk : 2 ≤ k) (f : dotted (1 / 2 : ℝ)) :
    halfDiskTraceCLM (jacobiExtensionCLM hk f) = f.val := jacobiExtensionH1_halfTrace hk f

lemma jacobiExtensionCLM_injective {k : ℕ} (hk : 2 ≤ k) :
    Function.Injective (jacobiExtensionCLM hk) := by
  intro f g h
  apply Subtype.ext
  have he := congrArg halfDiskTraceCLM h
  simpa only [jacobiExtensionCLM_halfTrace] using he

lemma jacobiExtensionCLM_weak_zeroTrace {k : ℕ} (hk : 2 ≤ k) (f : dotted (1 / 2 : ℝ))
    (v : ComplexH1) (hv : v ∈ zeroTraceDomain Set.univ) :
    weakJacobi (surfacePotential k) (jacobiExtensionCLM hk f) v = 0 :=
  jacobiExtensionH1_weak_zeroTrace hk f v hv

end KsIndex.Trace
