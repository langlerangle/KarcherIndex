module

public import KsIndexLean.HalfDiskFiniteEnergy
public import KsIndexLean.SmoothGermTrace
public import KsIndexLean.WeakDirichletModeSelection

@[expose] public section


/-! Identification of the weak trace with one-sided classical boundary values.
Deleted punctures are ignored only after proving that their circle measure is zero. -/
noncomputable section
open Set MeasureTheory Filter Topology
namespace KsIndex.Trace.ClassicalHalfDiskJacobi
open KsIndex.Surface KsIndex.SurfaceForm KsIndex.PunctureCutoff
variable {k : ℕ} {b : Bool} (u : ClassicalHalfDiskJacobi k b)

/-- The trace retains the classical values away from the deleted boundary points. -/
lemma trace_ae_off_punctures (hk : 2 ≤ k) :
    (diskTraceCLM (u.toH1 hk) : Circle₁ → ℂ) =ᵐ[
      circleMeasure.restrict {w : Circle₁ | (w : ℂ) ∉ punctures k}]
      (fun w => u.value w) := by
  apply ae_on_of_local_neighbourhoods
  intro x hx
  have hx1 := mem_sphere_zero_iff_norm.mp x.property
  obtain ⟨F, hF, hs, _⟩ := u.boundary x hx1 hx
  obtain ⟨O, hO, hxO, hFc⟩ := continuous_neighbourhood_of_smooth_germ hF
  obtain ⟨V, hVs, hV, hxV⟩ := eventually_nhds_iff.mp hs
  have hlocal : ∀ᵐ z ∂volume.restrict (WeakH1.disk : Set ℂ),
      z ∈ O ∩ V → WeakH1.valueCLM (u.toH1 hk) z = F z := by
    filter_upwards [u.toH1_value_ae hk, ae_restrict_mem Metric.isOpen_ball.measurableSet] with z hz hd hzOV
    exact hz.trans (hVs z hzOV.2 (mem_disk_iff.mp hd).le)
  obtain ⟨A, hA, hxA, ht⟩ := exists_boundary_neighbourhood_agreement (u.toH1 hk)
    (hO.inter hV) (hFc.mono inter_subset_left) ⟨hxO, hxV⟩ hlocal
  let B : Set Circle₁ := A ∩ (Subtype.val ⁻¹' V)
  have hB : IsOpen B := hA.inter (hV.preimage continuous_subtype_val)
  refine ⟨B, hB, ⟨hxA,hxV⟩, ?_⟩
  have htB := ht.filter_mono (ae_mono (Measure.restrict_mono (show B ⊆ A from inter_subset_left) le_rfl))
  filter_upwards [htB, ae_restrict_mem hB.measurableSet] with w hw hwB
  exact hw.trans (hVs w hwB.2 (mem_sphere_zero_iff_norm.mp w.property).le).symm

/-- Removing the finitely many punctures changes no circle-a.e. statement. -/
lemma circle_ae_not_puncture (hk : 1 ≤ k) :
    ∀ᵐ w : Circle₁ ∂circleMeasure, (w : ℂ) ∉ punctures k := by
  have hf : Set.Finite {w : Circle₁ | (w : ℂ) ∈ punctures k} := by
    have hp : Set.Finite (punctures k) := by
      convert (pF k).finite_toSet using 1
      ext w
      exact (mem_pF hk).symm
    exact hp.preimage Subtype.val_injective.injOn
  apply ae_iff.mpr
  have hnull : circleMeasure {w : Circle₁ | (w : ℂ) ∈ punctures k} = 0 := by
    rw [circleMeasure, Measure.map_apply measurable_circleParam hf.measurableSet,
      Measure.restrict_apply (measurable_circleParam hf.measurableSet)]
    have hi : Set.InjOn circleParam (Ico 0 (2 * Real.pi)) := by
      intro x hx y hy he
      apply injOn_circleMap_of_abs_sub_le' (c := 0) (R := 1)
        (by norm_num) (by linarith) hx hy
      exact congrArg Subtype.val he
    have hfin : (circleParam ⁻¹' {w : Circle₁ | (w : ℂ) ∈ punctures k} ∩
        Ico 0 (2 * Real.pi)).Finite := by
      apply Set.Finite.of_finite_image (f := circleParam)
      · apply hf.subset
        rintro _ ⟨x,hx,rfl⟩
        exact hx.1
      · exact hi.mono inter_subset_right
    exact hfin.measure_zero volume
  simpa only [not_not] using hnull

/-- The Sobolev trace equals the classical circle value almost everywhere. -/
theorem trace_ae (hk : 2 ≤ k) :
    (diskTraceCLM (u.toH1 hk) : Circle₁ → ℂ) =ᵐ[circleMeasure] (fun w => u.value w) := by
  have hfull : circleMeasure.restrict {w : Circle₁ | (w : ℂ) ∉ punctures k} = circleMeasure :=
    Measure.restrict_eq_self_of_ae_mem (circle_ae_not_puncture (by omega))
  simpa only [hfull] using u.trace_ae_off_punctures hk

/-- A classical Dirichlet field belongs to the actual zero-trace Sobolev domain. -/
theorem dirichlet_mem_zeroTrace (u : ClassicalHalfDiskJacobi k false) (hk : 2 ≤ k) :
    u.toH1 hk ∈ zeroTraceDomain Set.univ := by
  apply (mem_fullZeroTrace_iff _).mpr
  apply Lp.ext
  filter_upwards [u.trace_ae hk, circle_ae_not_puncture (by omega : 1 ≤ k),
    Lp.coeFn_zero (E := ℂ) (p := (2 : ENNReal)) (μ := circleMeasure)] with w ht hp hz
  obtain ⟨F,hF,hs,hD⟩ := u.boundary w (mem_sphere_zero_iff_norm.mp w.property) hp
  change F w = 0 at hD
  rw [ht, hz, hs.self_of_nhds (mem_sphere_zero_iff_norm.mp w.property).le, hD]
  rfl

end KsIndex.Trace.ClassicalHalfDiskJacobi
