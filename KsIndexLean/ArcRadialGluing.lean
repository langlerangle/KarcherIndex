module

public import KsIndexLean.WeakIntervalGluing
public import KsIndexLean.BoundaryRestriction

@[expose] public section


open Set MeasureTheory TauCeti

noncomputable section
namespace KsIndex.Trace
open KsIndex.WeakH1

/-- Bounded real-linear postcomposition preserves an interval weak derivative. -/
lemma weakInterval_comp {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    (L : E →L[ℝ] F) {a b : ℝ} {f g : ℝ → E}
    (h : HasWeakLineDerivOn volume (intervalOpens a b) f g 1) :
    HasWeakLineDerivOn volume (intervalOpens a b) (fun t => L (f t)) (fun t => L (g t)) 1 := by
  rw [hasWeakLineDerivOn_iff_testFunction]
  refine ⟨inferInstance, L.locallyIntegrableOn_comp h.locallyIntegrableOn,
    L.locallyIntegrableOn_comp h.locallyIntegrableOn_deriv, ?_⟩
  intro φ
  have hl := integrable_lineDeriv_smul_of_locallyIntegrableOn h.locallyIntegrableOn φ 1
  have hr := integrable_smul_of_locallyIntegrableOn h.locallyIntegrableOn_deriv φ
  calc
    _ = L (∫ t, lineDeriv ℝ (φ : ℝ → ℝ) t 1 • f t) := by
      simpa only [map_smul] using L.integral_comp_comm hl
    _ = -L (∫ t, (φ : ℝ → ℝ) t • g t) := by
      rw [h.integral_lineDeriv_smul_eq_neg_integral_smul φ, map_neg]
    _ = _ := by rw [← L.integral_comp_comm hr]; simp only [map_smul]

def arcProfile (A : Set Circle₁) (u : ComplexH1) : ℝ → Lp ℂ 2 (circleMeasure.restrict A) :=
  fun t => boundaryRestrictCLM A (diskProfile u t)

def arcRadialProfile (A : Set Circle₁) (u : ComplexH1) : ℝ → Lp ℂ 2 (circleMeasure.restrict A) :=
  fun t => boundaryRestrictCLM A (diskRadialProfile u t)

lemma arcProfile_weak (A : Set Circle₁) (u : ComplexH1) :
    HasWeakLineDerivOn volume (intervalOpens (1 / 2) 1) (arcProfile A u) (arcRadialProfile A u) 1 :=
  weakInterval_comp ((boundaryRestrictCLM A).restrictScalars ℝ) (disk_weak_polar u).2.2

lemma arcRadialProfile_integrable (A : Set Circle₁) (u : ComplexH1) :
    IntervalIntegrable (arcRadialProfile A u) volume (1 / 2) 1 :=
  ⟨(boundaryRestrictCLM A).integrable_comp (disk_weak_polar u).2.1.1,
    (boundaryRestrictCLM A).integrable_comp (disk_weak_polar u).2.1.2⟩

/-- The interval representative of the restricted profile has exactly the genuine arc trace. -/
lemma arcProfile_endpoint (A : Set Circle₁) (u : ComplexH1) :
    representative (by norm_num : (1 / 2 : ℝ) < 1) (arcProfile A u) (arcRadialProfile A u) 1 =
      arcTrace A u := by
  have hc := (boundaryRestrictCLM A).continuous.comp_continuousOn
    (diskRepresentative_continuousOn u)
  have he : (fun t => boundaryRestrictCLM A (diskRepresentative u t))
      =ᵐ[volume.restrict (Ioo (1 / 2 : ℝ) 1)] arcProfile A u := by
    filter_upwards [diskRepresentative_ae u] with t ht
    exact congrArg (boundaryRestrictCLM A) ht.symm
  exact (representative_unique (by norm_num) (arcProfile_weak A u)
    (arcRadialProfile_integrable A u) hc he (by norm_num : (1 : ℝ) ∈ Icc (1 / 2) 1)).symm

/-- Radial gluing on a boundary arc is governed by the actual restricted disk trace. -/
theorem arcProfile_gluing_iff (A : Set Circle₁) (u : ComplexH1) {b : ℝ} (hb : 1 < b)
    {p h : ℝ → Lp ℂ 2 (circleMeasure.restrict A)}
    (hp : HasWeakLineDerivOn volume (intervalOpens 1 b) p h 1)
    (hh : IntervalIntegrable h volume 1 b) :
    HasWeakLineDerivOn volume (intervalOpens (1 / 2) b)
      (joinAt 1 (arcProfile A u) p) (joinAt 1 (arcRadialProfile A u) h) 1 ↔
      arcTrace A u = representative hb p h 1 := by
  rw [weak_joinAt_iff_match (by norm_num) hb (arcProfile_weak A u) hp
    (arcRadialProfile_integrable A u) hh, arcProfile_endpoint]

end KsIndex.Trace
