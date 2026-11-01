module

public import KsIndexLean.MollificationSupport
public import KsIndexLean.SlitSeamGauges
public import KsIndexLean.CollarInversionBound

@[expose] public section


open Set Filter Topology MeasureTheory
noncomputable section
namespace KsIndex.Trace
open KsIndex.Bracket KsIndex.WeakH1

lemma seamDomain_sigma {A : Set Circle₁} (hA : IsOpen A) :
    MapsTo σ (seamDomain A hA) (seamDomain A hA) := by
  intro z hz
  have hz' := (mem_seamDomain_iff hA z).mp hz
  apply (mem_seamDomain_iff hA (σ z)).mpr
  refine ⟨sigma_mem_symmetric_collar hz'.1, ?_⟩
  intro w hw
  apply hz'.2 w
  have hn : ‖(w : ℂ)‖ = 1 := mem_sphere_zero_iff_norm.mp w.property
  calc
    (w : ℂ) = σ (w : ℂ) := (σ_self hn).symm
    _ = z := by rw [hw, σ_σ]

lemma zero_notMem_seamDomain {A : Set Circle₁} (hA : IsOpen A) :
    (0 : ℂ) ∉ seamDomain A hA := by
  intro hz
  have hh := hz.1.1
  norm_num at hh

/-- Reflection smoothing of a localized seam function stays within its actual seam domain. -/
theorem reflected_mollifier_support_seam (s : ℂ) {A : Set Circle₁} (hA : IsOpen A)
    {u : ℂ → ℂ} (hc : HasCompactSupport u) (hs : tsupport u ⊆ seamDomain A hA) :
    ∀ᶠ n in atTop,
      tsupport (reflectionAverage s (compactMollify (shrinkingMollifier n) u)) ⊆
        seamDomain A hA :=
  reflected_mollifier_support_open s hc (seamDomain A hA).isOpen hs
    (zero_notMem_seamDomain hA) (seamDomain_sigma hA)

end KsIndex.Trace
