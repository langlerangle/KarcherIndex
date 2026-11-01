module

public import KsIndexLean.MixedHalfDiskFiniteEnergy
public import KsIndexLean.ClosedSideGermTrace
public import KsIndexLean.HalfDiskTrace
public import KsIndexLean.DiskRotationForms

@[expose] public section


/-! The Sobolev trace of a bounded mixed classical field retains its actual
boundary values and hence its Dirichlet conditions on the prescribed arcs. -/
noncomputable section
open Set MeasureTheory Filter Topology
namespace KsIndex.Trace.ClassicalMixedHalfDiskJacobi
open KsIndex.Surface KsIndex.SurfaceForm
variable {k : ℕ} {b1 b0 : Bool} (u : ClassicalMixedHalfDiskJacobi k b1 b0)

lemma trace_ae_off_punctures (hk : 2 ≤ k) :
    (diskTraceCLM (u.toH1 hk) : Circle₁ → ℂ) =ᵐ[
      circleMeasure.restrict {w : Circle₁ | (w : ℂ) ∉ punctures k}]
      (fun w => u.value w) := by
  apply diskTrace_closed_side_germs _ (u.toH1_value_ae hk)
  intro w hw
  obtain ⟨F, hF, hs, _⟩ := u.boundary w (mem_sphere_zero_iff_norm.mp w.property) hw
  exact ⟨F, hF, hs⟩

theorem trace_ae (hk : 2 ≤ k) :
    (diskTraceCLM (u.toH1 hk) : Circle₁ → ℂ) =ᵐ[circleMeasure] (fun w => u.value w) := by
  have hfull : circleMeasure.restrict {w : Circle₁ | (w : ℂ) ∉ punctures k} = circleMeasure :=
    Measure.restrict_eq_self_of_ae_mem
      (ClassicalHalfDiskJacobi.circle_ae_not_puncture (by omega))
  simpa only [hfull] using u.trace_ae_off_punctures hk

/-- Both arc conditions hold in the genuine trace domain. No normal condition
is imposed on arbitrary weak tests at the Neumann arcs. -/
theorem toH1_mem_mixed (hk : 2 ≤ k) : u.toH1 hk ∈ mixedTraceDomain k b1 b0 := by
  have ht (a : ℕ) : (diskTraceCLM (u.toH1 hk) : Circle₁ → ℂ)
      =ᵐ[circleMeasure.restrict (boundaryArc k a)] (fun w => u.value w) :=
    (u.trace_ae hk).filter_mono (ae_mono Measure.restrict_le_self)
  have hp (a : ℕ) : ∀ᵐ w : Circle₁ ∂circleMeasure.restrict (boundaryArc k a),
      (w : ℂ) ∉ punctures k :=
    (ClassicalHalfDiskJacobi.circle_ae_not_puncture (by omega : 1 ≤ k)).filter_mono
      (ae_mono Measure.restrict_le_self)
  constructor
  · apply (mem_naturalArcDomain k 1 b1 _).mpr
    intro hflag
    filter_upwards [ht 1, hp 1, ae_restrict_mem (measurableSet_boundaryArc k 1)]
      with w hw hpw haw
    obtain ⟨F, _hF, hs, h1, _⟩ := u.boundary w (mem_sphere_zero_iff_norm.mp w.property) hpw
    have hz := h1 haw
    simp only [hflag, Bool.false_eq_true, ite_false] at hz
    exact hw.trans ((hs.self_of_nhds (mem_sphere_zero_iff_norm.mp w.property).le).trans hz)
  · apply (mem_naturalArcDomain k 0 b0 _).mpr
    intro hflag
    filter_upwards [ht 0, hp 0, ae_restrict_mem (measurableSet_boundaryArc k 0)]
      with w hw hpw haw
    obtain ⟨F, _hF, hs, _, h0⟩ := u.boundary w (mem_sphere_zero_iff_norm.mp w.property) hpw
    have hz := h0 haw
    simp only [hflag, Bool.false_eq_true, ite_false] at hz
    exact hw.trans ((hs.self_of_nhds (mem_sphere_zero_iff_norm.mp w.property).le).trans hz)

/-- Only the interior character equation is needed; no condition is imposed
on the arbitrary exterior values of a classical representative. -/
lemma toH1_character (hk : 2 ≤ k) (θ : ℝ) (c : ℂ)
    (hchar : ∀ w ∈ Surface.disk, u.value (planeRotation θ w) = c * u.value w) :
    u.toH1 hk ∈ weakCharacterDomain θ c := by
  apply (mem_weakCharacterDomain θ c _).mpr
  apply WeakH1.valueCLM_injective
  rw [map_smul]
  apply Lp.ext
  have hr := (measurePreserving_planeRotation_disk θ).quasiMeasurePreserving.ae_eq_comp
    (u.toH1_value_ae hk)
  filter_upwards [diskRotation_value_ae θ (u.toH1 hk), hr, u.toH1_value_ae hk,
    Lp.coeFn_smul c (WeakH1.valueCLM (u.toH1 hk)),
    ae_restrict_mem WeakH1.disk.isOpen.measurableSet] with w hrot hrw huw hcw hw
  rw [hrot, hcw]
  change WeakH1.valueCLM (u.toH1 hk) (planeRotation θ w) = c * WeakH1.valueCLM (u.toH1 hk) w
  change WeakH1.valueCLM (u.toH1 hk) (planeRotation θ w) = u.value (planeRotation θ w) at hrw
  rw [hrw, huw, hchar w hw]

theorem toH1_mem_mixedCharacter (hk : 2 ≤ k) (j : ℕ)
    (hchar : ∀ w ∈ Surface.disk,
      u.value (planeRotation (-(2 * Real.pi) / k) w) = FormIndex.zeta k ^ j * u.value w) :
    u.toH1 hk ∈ mixedCharacterDomain k j b1 b0 :=
  ⟨u.toH1_mem_mixed hk, u.toH1_character hk _ _ hchar⟩

end KsIndex.Trace.ClassicalMixedHalfDiskJacobi
