module

public import KsIndexLean.DiskH1RotationIsometry
public import Mathlib.MeasureTheory.Function.LpSpace.ContinuousCompMeasurePreserving

@[expose] public section


noncomputable section
open Set MeasureTheory
namespace KsIndex.Trace
open KsIndex.WeakH1

lemma continuous_planeRotation_parameter (z : ℂ) : Continuous (fun θ : ℝ => planeRotation θ z) := by
  simp only [planeRotation_apply]
  fun_prop

lemma continuous_diskLpRotation (f : L2C) : Continuous (fun θ : ℝ => diskLpRotation θ f) := by
  let g : ℝ → C(ℂ, ℂ) := fun θ => ⟨planeRotation θ, (planeRotation θ).continuous⟩
  have hg : Continuous g := by
    apply ContinuousMap.continuous_of_continuous_uncurry
    change Continuous (fun p : ℝ × ℂ => planeRotation p.1 p.2)
    simp only [planeRotation_apply]
    fun_prop
  exact continuous_const.compMeasurePreservingLp hg measurePreserving_planeRotation_disk (by norm_num)

lemma rotatedColumn_eq (θ : ℝ) (u : ComplexH1) (v : ℂ) :
    rotatedColumn θ u v = (planeRotation θ v).re • diskLpRotation θ (dxLp u) +
      (planeRotation θ v).im • diskLpRotation θ (dyLp u) := by
  apply Lp.ext
  filter_upwards [rotatedColumn_coe_ae θ u v, diskLpRotation_coe_ae θ (dxLp u),
    diskLpRotation_coe_ae θ (dyLp u),
    Lp.coeFn_smul ((planeRotation θ v).re) (diskLpRotation θ (dxLp u)),
    Lp.coeFn_smul ((planeRotation θ v).im) (diskLpRotation θ (dyLp u)),
    Lp.coeFn_add ((planeRotation θ v).re • diskLpRotation θ (dxLp u))
      ((planeRotation θ v).im • diskLpRotation θ (dyLp u))] with z hz hx hy hs ht ha
  rw [hz, ha, Pi.add_apply, hs, ht]
  simp only [Pi.smul_apply, hx, hy, Function.comp_apply, Dxy_apply, Complex.real_smul]

lemma continuous_rotatedColumn (u : ComplexH1) (v : ℂ) :
    Continuous (fun θ : ℝ => rotatedColumn θ u v) := by
  simp_rw [rotatedColumn_eq]
  exact ((Complex.continuous_re.comp (continuous_planeRotation_parameter v)).smul (continuous_diskLpRotation (dxLp u))).add
    ((Complex.continuous_im.comp (continuous_planeRotation_parameter v)).smul (continuous_diskLpRotation (dyLp u)))

lemma continuous_diskRotation (u : ComplexH1) : Continuous (fun θ : ℝ => diskRotation θ u) := by
  apply continuous_iff_continuousAt.mpr
  intro θ
  rw [ContinuousAt, tendsto_iff_norm_sub_tendsto_zero]
  have hv : Continuous (fun a : ℝ => valueCLM (diskRotation a u)) := by
    change Continuous (fun a => valueCLM (diskH1Rotation a u))
    simp_rw [diskH1Rotation_value]
    exact continuous_diskLpRotation _
  have hx : Continuous (fun a : ℝ => dxLp (diskRotation a u)) := by
    change Continuous (fun a => dxLp (diskH1Rotation a u))
    simp_rw [(diskH1Rotation_coordinates _ _).1]
    exact continuous_rotatedColumn u 1
  have hy : Continuous (fun a : ℝ => dyLp (diskRotation a u)) := by
    change Continuous (fun a => dyLp (diskH1Rotation a u))
    simp_rw [(diskH1Rotation_coordinates _ _).2]
    exact continuous_rotatedColumn u Complex.I
  have hn (a : ℝ) : ‖diskRotation a u - diskRotation θ u‖ =
      Real.sqrt (‖valueCLM (diskRotation a u) - valueCLM (diskRotation θ u)‖ ^ 2 +
        ‖dxLp (diskRotation a u) - dxLp (diskRotation θ u)‖ ^ 2 +
        ‖dyLp (diskRotation a u) - dyLp (diskRotation θ u)‖ ^ 2) := by
    have h := coordinate_graph_norm_sq (diskRotation a u - diskRotation θ u)
    change ‖diskRotation a u - diskRotation θ u‖ ^ 2 =
      ‖valueCLM (diskRotation a u - diskRotation θ u)‖ ^ 2 +
      ‖dxCLM (diskRotation a u - diskRotation θ u)‖ ^ 2 +
      ‖dyCLM (diskRotation a u - diskRotation θ u)‖ ^ 2 at h
    simp only [map_sub] at h
    have h' : ‖diskRotation a u - diskRotation θ u‖ ^ 2 =
      ‖valueCLM (diskRotation a u) - valueCLM (diskRotation θ u)‖ ^ 2 +
      ‖dxLp (diskRotation a u) - dxLp (diskRotation θ u)‖ ^ 2 +
      ‖dyLp (diskRotation a u) - dyLp (diskRotation θ u)‖ ^ 2 := h
    rw [← h', Real.sqrt_sq (norm_nonneg _)]
  simp_rw [hn]
  have hc : Continuous (fun a : ℝ => Real.sqrt
      (‖valueCLM (diskRotation a u) - valueCLM (diskRotation θ u)‖ ^ 2 +
      ‖dxLp (diskRotation a u) - dxLp (diskRotation θ u)‖ ^ 2 +
      ‖dyLp (diskRotation a u) - dyLp (diskRotation θ u)‖ ^ 2)) :=
    (((hv.sub continuous_const).norm.pow 2).add
    ((hx.sub continuous_const).norm.pow 2) |>.add
    ((hy.sub continuous_const).norm.pow 2)).sqrt
  simpa only [ContinuousAt, sub_self, norm_zero, ne_eq, OfNat.ofNat_ne_zero,
    not_false_eq_true, zero_pow, zero_add, Real.sqrt_zero] using hc.continuousAt (x := θ)

end KsIndex.Trace
