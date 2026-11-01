module

public import KsIndexLean.SeamDomainWeakGluing
public import KsIndexLean.SlitInversionCharts
public import KsIndexLean.SmoothReflectionProjection

@[expose] public section


open Set MeasureTheory
noncomputable section
namespace KsIndex.Trace
open KsIndex.WeakH1 KsIndex.SingleDisk

lemma joined_self_eq_refl (u : ComplexH1) (s : ℂ) :
    joinedDiskValue u u s = refl s (valueCLM u) := by
  funext z
  rw [joinedDiskValue_sigma_formula]
  rfl

/-- The paper's reflected function is an actual weak extension when its traces match. -/
theorem weak_refl_extension {A : Set Circle₁} (hA : IsOpen A) (u : ComplexH1) (s : ℂ)
    (hm : arcTrace A u = s • arcTrace A u) :
    TauCeti.HasWeakFDerivOn volume (seamDomain A hA)
      (refl s (valueCLM u)) (joinedDiskJet u u s) := by
  rw [← joined_self_eq_refl]
  exact seamDomain_weak_gluing hA u u s hm

/-- Even weak extension imposes no trace boundary condition. -/
theorem weak_even_extension {A : Set Circle₁} (hA : IsOpen A) (u : ComplexH1) :
    TauCeti.HasWeakFDerivOn volume (seamDomain A hA)
      (refl 1 (valueCLM u)) (joinedDiskJet u u 1) :=
  weak_refl_extension hA u 1 (by rw [one_smul])

/-- Odd weak extension is available for the actual zero-trace domain. -/
theorem weak_odd_extension {A : Set Circle₁} (hA : IsOpen A) (u : ComplexH1)
    (hu : u ∈ zeroTraceDomain A) :
    TauCeti.HasWeakFDerivOn volume (seamDomain A hA)
      (refl (-1) (valueCLM u)) (joinedDiskJet u u (-1)) := by
  apply weak_refl_extension hA u (-1)
  change arcTrace A u = 0 at hu
  rw [hu, smul_zero]

lemma refl_value_memLp {A : Set Circle₁} (hA : IsOpen A) (u : ComplexH1) (s : ℂ) :
    MemLp (refl s (valueCLM u)) 2 (volume.restrict (seamDomain A hA : Set ℂ)) := by
  rw [← joined_self_eq_refl]
  exact seamDomain_value_memLp hA u u s

lemma refl_direction_memLp {A : Set Circle₁} (hA : IsOpen A)
    (u : ComplexH1) (s d : ℂ) :
    MemLp (fun z => joinedDiskJet u u s z d) 2
      (volume.restrict (seamDomain A hA : Set ℂ)) :=
  (seamDomain_jet_memLp hA u u s).continuousLinearMap_comp
    (ContinuousLinearMap.apply ℝ ℂ d)

end KsIndex.Trace
