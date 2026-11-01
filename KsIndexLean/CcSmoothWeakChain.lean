module

public import KsIndexLean.ChainChartNormed
public import KsIndexLean.PhaseGermTrace
public import KsIndexLean.NaturalCoreForm

@[expose] public section


open Set MeasureTheory
open scoped ContDiff
noncomputable section
namespace KsIndex.Trace
open KsIndex.WeakH1

/-- Compactly supported smooth copies have finite value and derivative L2 norms.
No seam-value representative normalization is assumed. -/
lemma ccSmooth_copy_memLp {k m : ℕ} (u : Surface.CcSmooth k m) (n : ZMod (2 * m)) :
    MemLp (u.val n) 2 (volume.restrict (disk : Set ℂ)) ∧
    MemLp (fun z => fderiv ℝ (u.val n) z 1) 2 (volume.restrict (disk : Set ℂ)) ∧
    MemLp (fun z => fderiv ℝ (u.val n) z Complex.I) 2 (volume.restrict (disk : Set ℂ)) := by
  let : IsFiniteMeasure (volume.restrict (disk : Set ℂ)) :=
    ⟨by simp [disk]⟩
  let : IsFiniteMeasure (volume.restrict Surface.disk) :=
    inferInstanceAs (IsFiniteMeasure (volume.restrict (disk : Set ℂ)))
  have hr := SurfaceForm.regular_of_mem u.property
  obtain ⟨M, hM⟩ := SurfaceForm.exists_bound_val hr n
  obtain ⟨N, hN⟩ := SurfaceForm.exists_bound_fderiv hr n
  have hval : MemLp (u.val n) 2 (volume.restrict (disk : Set ℂ)) := by
    apply MemLp.of_bound ((hr.1 n).continuousOn.aestronglyMeasurable
      disk.isOpen.measurableSet) M
    exact ae_restrict_of_forall_mem disk.isOpen.measurableSet hM
  have hd (v : ℂ) : MemLp (fun z => fderiv ℝ (u.val n) z v) 2
      (volume.restrict (disk : Set ℂ)) := by
    apply MemLp.of_bound (measurable_fderiv_apply_const ℝ (u.val n) v).aestronglyMeasurable.restrict
      (N * ‖v‖)
    refine ae_restrict_of_forall_mem disk.isOpen.measurableSet fun z hz => ?_
    exact (ContinuousLinearMap.le_opNorm _ _).trans
      (mul_le_mul_of_nonneg_right (hN z hz) (norm_nonneg v))
  exact ⟨hval, hd 1, hd Complex.I⟩

def ccSmoothCopyData {k m : ℕ} (u : Surface.CcSmooth k m) (n : ZMod (2 * m)) :
    SmoothH1Data where
  F := u.val n
  smooth := u.property.1.1 n
  value_mem := (ccSmooth_copy_memLp u n).1
  dx_mem := (ccSmooth_copy_memLp u n).2.1
  dy_mem := (ccSmooth_copy_memLp u n).2.2

def ccSmoothCopy {k m : ℕ} (u : Surface.CcSmooth k m) (n : ZMod (2 * m)) : ComplexH1 :=
  smoothToH1 (ccSmoothCopyData u n)

lemma ccSmoothCopy_value_ae {k m : ℕ} (u : Surface.CcSmooth k m) (n : ZMod (2 * m)) :
    (valueCLM (ccSmoothCopy u n) : ℂ → ℂ) =ᵐ[volume.restrict (disk : Set ℂ)] u.val n :=
  smoothToH1_value_ae _

/-- Smooth seam germs imply equality of the actual Sobolev traces. -/
lemma ccSmoothCopy_seam {k m : ℕ} (u : Surface.CcSmooth k m) (n : ZMod (2 * m)) :
    arcTrace (seamBoundary k m n) (ccSmoothCopy u n) =
      arcTrace (seamBoundary k m n) (ccSmoothCopy u (n + 1)) := by
  have he : phaseGerm 1 (u.val n) (u.val (n + 1)) = Surface.glue u.val n := by
    funext z
    simp only [phaseGerm, Surface.glue, one_mul, Bracket.σ_apply]
  have h := arcTrace_phaseGerm (A := seamBoundary k m n)
    (ccSmoothCopy u n) (ccSmoothCopy u (n + 1)) 1
    (ccSmoothCopy_value_ae u n) (ccSmoothCopy_value_ae u (n + 1))
    (by rw [he]; exact fun w hw => u.property.1.2.1 n w hw)
  simpa only [one_smul] using h

lemma ccSmoothCopy_add {k m : ℕ} (u v : Surface.CcSmooth k m) (n : ZMod (2 * m)) :
    ccSmoothCopy (u + v) n = ccSmoothCopy u n + ccSmoothCopy v n := by
  apply valueCLM_injective
  rw [map_add]
  apply Lp.ext
  filter_upwards [ccSmoothCopy_value_ae (u + v) n, ccSmoothCopy_value_ae u n,
    ccSmoothCopy_value_ae v n,
    Lp.coeFn_add (valueCLM (ccSmoothCopy u n)) (valueCLM (ccSmoothCopy v n))]
    with z hs hu hv ha
  rw [ha, Pi.add_apply, hs, hu, hv]
  rfl

lemma ccSmoothCopy_smul {k m : ℕ} (c : ℂ) (u : Surface.CcSmooth k m) (n : ZMod (2 * m)) :
    ccSmoothCopy (c • u) n = c • ccSmoothCopy u n := by
  apply valueCLM_injective
  rw [map_smul]
  apply Lp.ext
  filter_upwards [ccSmoothCopy_value_ae (c • u) n, ccSmoothCopy_value_ae u n,
    Lp.coeFn_smul c (valueCLM (ccSmoothCopy u n))] with z hs hu hc
  rw [hc, Pi.smul_apply, hs, hu]
  rfl

/-- The original smooth test space maps directly to the weak chain.
This map need not be injective on total-function representatives. -/
def ccSmoothToWeakChain (k m : ℕ) [NeZero m] :
    Surface.CcSmooth k m →ₗ[ℂ] weakDiskChain k m where
  toFun u := ⟨ccSmoothCopy u, (mem_weakDiskChain k m _).mpr (ccSmoothCopy_seam u)⟩
  map_add' u v := Subtype.ext (funext (ccSmoothCopy_add u v))
  map_smul' c u := Subtype.ext (funext (ccSmoothCopy_smul c u))

def ccSmoothToChainChart (k m : ℕ) [NeZero m] :
    Surface.CcSmooth k m →ₗ[ℂ] ChainChartSpace k m :=
  (chainChartLinearIsometryEquiv k m).symm.toLinearEquiv.toLinearMap.comp
    (ccSmoothToWeakChain k m)

lemma ccSmoothToChainChart_coordinates (k m : ℕ) [NeZero m]
    (u : Surface.CcSmooth k m) :
    chainChartCoordinatesCLM k m (ccSmoothToChainChart k m u) = ccSmoothCopy u :=
  chainChartCoordinates_class k m (ccSmoothToWeakChain k m u)

end KsIndex.Trace
