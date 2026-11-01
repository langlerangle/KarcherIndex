module

public import KsIndexLean.WeakOpenEquation
public import KsIndexLean.WeakSmoothRepresentative

@[expose] public section


/-! Interior smooth representatives directly from the concrete weak first jet.
The potential is smooth on the coordinate plane, but the equation and all L²
hypotheses are imposed only on the open coordinate domain. The conclusions are
local smooth representatives and smoothness of a supplied continuous representative. -/
noncomputable section
open Set MeasureTheory TopologicalSpace
open scoped SchwartzMap BoundedContinuousFunction
namespace KsIndex.Weq

/-- A concrete interior weak solution has a smooth representative near every
interior point. All distributional bootstrap inputs are discharged here. -/
theorem exists_smooth_near_of_interior_weak_jet
    {Ω : Opens ℂ} {u ux uy V : ℂ → ℂ}
    (hu : MemLp u 2 (volume.restrict (Ω : Set ℂ)))
    (hx2 : MemLp ux 2 (volume.restrict (Ω : Set ℂ)))
    (hy2 : MemLp uy 2 (volume.restrict (Ω : Set ℂ)))
    (hq2 : MemLp (fun z => V z * u z) 2 (volume.restrict (Ω : Set ℂ)))
    (hx : TauCeti.HasWeakLineDerivOn volume Ω u ux 1)
    (hy : TauCeti.HasWeakLineDerivOn volume Ω u uy Complex.I)
    (heq : InteriorWeakEquation Ω ux uy (fun z => V z * u z))
    (hV : ContDiff ℝ (⊤ : ℕ∞) V) {z : ℂ} (hz : z ∈ (Ω : Set ℂ)) :
    ∃ r : ℝ, 0 < r ∧ Metric.ball z r ⊆ (Ω : Set ℂ) ∧ ∃ g : ℂ →ᵇ ℂ,
      ContDiff ℝ (⊤ : ℕ∞) (g : ℂ → ℂ) ∧
      u =ᵐ[volume.restrict (Metric.ball z r)] g := by
  have he := localPotentialEquation_openDist hu hx hy heq hV
  have hS := (localMemSobolev_two_openDist hu hx2 hy2 hq2 hx hy heq).mono
    (show (1 : ℝ) ≤ 2 by norm_num)
  obtain ⟨r, hr, hs, g, hg, hag⟩ := exists_smooth_near_of_local_potential
    (openExtend u hu) Ω.isOpen hV he hS hz
  refine ⟨r, hr, hs, g, hg, ?_⟩
  have hloc := ae_restrict_of_ae (s := Metric.ball z r) (openExtend_ae u hu)
  filter_upwards [hloc, hag, ae_restrict_mem measurableSet_ball] with x hx' hg' hxb
  rw [Set.indicator_of_mem (hs hxb)] at hx'
  exact hx'.symm.trans hg'

/-- If a continuous representative is already supplied by the chart/seam
construction, its smoothness follows pointwise from the same weak equation. -/
theorem contDiffOn_of_continuous_interior_weak_jet
    {Ω : Opens ℂ} {u ux uy V : ℂ → ℂ}
    (hu : MemLp u 2 (volume.restrict (Ω : Set ℂ)))
    (hx2 : MemLp ux 2 (volume.restrict (Ω : Set ℂ)))
    (hy2 : MemLp uy 2 (volume.restrict (Ω : Set ℂ)))
    (hq2 : MemLp (fun z => V z * u z) 2 (volume.restrict (Ω : Set ℂ)))
    (hx : TauCeti.HasWeakLineDerivOn volume Ω u ux 1)
    (hy : TauCeti.HasWeakLineDerivOn volume Ω u uy Complex.I)
    (heq : InteriorWeakEquation Ω ux uy (fun z => V z * u z))
    (hV : ContDiff ℝ (⊤ : ℕ∞) V) (hc : ContinuousOn u (Ω : Set ℂ)) :
    ContDiffOn ℝ (⊤ : ℕ∞) u (Ω : Set ℂ) := by
  have he := localPotentialEquation_openDist hu hx hy heq hV
  have hS := (localMemSobolev_two_openDist hu hx2 hy2 hq2 hx hy heq).mono
    (show (1 : ℝ) ≤ 2 by norm_num)
  apply contDiffOn_of_continuous_representative_local_potential
    (openExtend u hu) Ω.isOpen hV he hS hc
  filter_upwards [ae_restrict_of_ae (s := (Ω : Set ℂ)) (openExtend_ae u hu),
    ae_restrict_mem Ω.isOpen.measurableSet] with x hx' hxo
  simpa only [Set.indicator_of_mem hxo] using hx'

end KsIndex.Weq
