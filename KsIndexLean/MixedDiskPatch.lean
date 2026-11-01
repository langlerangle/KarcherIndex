module

public import KsIndexLean.MixedDNReflection
public import KsIndexLean.SeamRepresentativeCompatibility
public import KsIndexLean.JacobiFamily
public import KsIndexLean.SmoothRepresentativeEnergy

@[expose] public section


/-!
# Patching the interior and mixed boundary representatives

The two reflected fields agree with the interior field on the inner collar.
Their exterior values need not agree with one another. Selecting the field
according to the sign of Re(z^k) preserves each boundary germ separately.
-/
noncomputable section
open Set MeasureTheory Filter Topology
namespace KsIndex.Trace
open KsIndex.WeakH1 KsIndex.Surface KsIndex.FormIndex

/-- Interior values with the appropriate reflected representative near each arc. -/
def mixedDiskPatch (k : ℕ) (f F0 F1 : ℂ → ℂ) (z : ℂ) : ℂ :=
  if ‖z‖ < 1 then f z else if (z ^ k).re < 0 then F0 z else F1 z

lemma mixedDiskPatch_inner (k : ℕ) (f F0 F1 : ℂ → ℂ) :
    EqOn (mixedDiskPatch k f F0 F1) f (WeakH1.disk : Set ℂ) := by
  intro z hz
  have hi : ‖z‖ < 1 := by
    change z ∈ Metric.ball (0 : ℂ) 1 at hz
    simpa only [Metric.mem_ball, dist_zero_right] using hz
  simp only [mixedDiskPatch, ite_eq_left hi]

lemma mixedDiskPatch_dirichlet_germ (k : ℕ) (f F0 F1 : ℂ → ℂ)
    (hm : EqOn F0 f (annulusSet (1 / 2 : ℝ) 1))
    {w : ℂ} (hw : w ∈ arc k 0) :
    mixedDiskPatch k f F0 F1 =ᶠ[nhds w] F0 := by
  have hn : ∀ᶠ z : ℂ in nhds w, (1 / 2 : ℝ) < ‖z‖ :=
    (isOpen_lt continuous_const continuous_norm).mem_nhds (by change (1 / 2 : ℝ) < ‖w‖; rw [hw.1]; norm_num)
  have hrw : (w ^ k).re < 0 := by simpa [arc] using hw.2
  have hr : ∀ᶠ z : ℂ in nhds w, (z ^ k).re < 0 :=
    (isOpen_lt (by fun_prop) continuous_const).mem_nhds hrw
  filter_upwards [hn, hr] with z hn hr
  by_cases hi : ‖z‖ < 1
  · simpa only [mixedDiskPatch, ite_eq_left hi] using (hm ⟨hn, hi⟩).symm
  · simp only [mixedDiskPatch, ite_eq_right hi, ite_eq_left hr]

lemma mixedDiskPatch_neumann_germ (k : ℕ) (f F0 F1 : ℂ → ℂ)
    (hm : EqOn F1 f (annulusSet (1 / 2 : ℝ) 1))
    {w : ℂ} (hw : w ∈ arc k 1) :
    mixedDiskPatch k f F0 F1 =ᶠ[nhds w] F1 := by
  have hn : ∀ᶠ z : ℂ in nhds w, (1 / 2 : ℝ) < ‖z‖ :=
    (isOpen_lt continuous_const continuous_norm).mem_nhds (by change (1 / 2 : ℝ) < ‖w‖; rw [hw.1]; norm_num)
  have hrw : 0 < (w ^ k).re := by
    have h := hw.2
    simp only [pow_one, neg_one_mul] at h
    linarith
  have hr : ∀ᶠ z : ℂ in nhds w, 0 < (z ^ k).re :=
    (isOpen_lt continuous_const (by fun_prop)).mem_nhds hrw
  filter_upwards [hn, hr] with z hn hr
  by_cases hi : ‖z‖ < 1
  · simpa only [mixedDiskPatch, ite_eq_left hi] using (hm ⟨hn, hi⟩).symm
  · simp only [mixedDiskPatch, ite_eq_right hi, ite_eq_right (not_lt_of_ge hr.le)]

/-- The patched function retains its interior equation and values. -/
theorem mixedDiskPatch_interior (k : ℕ) (f F0 F1 : ℂ → ℂ)
    (hf : ContDiffOn ℝ (⊤ : ℕ∞) f (WeakH1.disk : Set ℂ))
    (he : ∀ z ∈ (WeakH1.disk : Set ℂ), laplacian f z + (potV k z : ℂ) * f z = 0) :
    ContDiffOn ℝ (⊤ : ℕ∞) (mixedDiskPatch k f F0 F1) (WeakH1.disk : Set ℂ) ∧
      ∀ z ∈ (WeakH1.disk : Set ℂ),
        laplacian (mixedDiskPatch k f F0 F1) z +
          (potV k z : ℂ) * mixedDiskPatch k f F0 F1 z = 0 := by
  have hg : ∀ z ∈ (WeakH1.disk : Set ℂ), mixedDiskPatch k f F0 F1 =ᶠ[nhds z] f :=
    fun z hz => Filter.eventuallyEq_of_mem (WeakH1.disk.isOpen.mem_nhds hz)
      (mixedDiskPatch_inner k f F0 F1)
  constructor
  · intro z hz
    exact ((hf.contDiffAt (WeakH1.disk.isOpen.mem_nhds hz)).congr_of_eventuallyEq
      (hg z hz)).contDiffWithinAt
  · intro z hz
    rw [JacobiFamily.laplacian_congr (hg z hz), (hg z hz).self_of_nhds]
    exact he z hz

/-- Changing the boundary/exterior representative preserves the original H¹ value. -/
lemma mixedDiskPatch_value_ae (k : ℕ) (u : ComplexH1) (f F0 F1 : ℂ → ℂ)
    (ha : valueCLM u =ᵐ[volume.restrict (WeakH1.disk : Set ℂ)] f) :
    valueCLM u =ᵐ[volume.restrict (WeakH1.disk : Set ℂ)] mixedDiskPatch k f F0 F1 := by
  filter_upwards [ha, ae_restrict_mem WeakH1.disk.isOpen.measurableSet] with z hz hd
  exact hz.trans (mixedDiskPatch_inner k f F0 F1 hd).symm

/-- The patched classical representative inherits finite gradient energy from H¹.
No boundedness hypothesis is involved. -/
theorem mixedDiskPatch_energy_integrable (k : ℕ) (u : ComplexH1) (f F0 F1 : ℂ → ℂ)
    (hf : ContDiffOn ℝ (⊤ : ℕ∞) f (WeakH1.disk : Set ℂ))
    (ha : valueCLM u =ᵐ[volume.restrict (WeakH1.disk : Set ℂ)] f)
    (he : ∀ z ∈ (WeakH1.disk : Set ℂ), laplacian f z + (potV k z : ℂ) * f z = 0) :
    IntegrableOn (gradSq (mixedDiskPatch k f F0 F1)) (WeakH1.disk : Set ℂ) :=
  Weq.smooth_representative_energy_integrable u
    (mixedDiskPatch_interior k f F0 F1 hf he).1
    (mixedDiskPatch_value_ae k u f F0 F1 ha)

end KsIndex.Trace
