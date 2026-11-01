module

/-
The gradient-energy carrier for smooth fields on the finite chain.

`GradEnergySmooth` requires smoothness, integrable Dirichlet density on each
disk copy, and the representative normalizations `PunctureZero` and `SeamVal`.
It does not assume per-copy value integrability in `L²`. This keeps the carrier
aligned with a finite-Dirichlet-energy hypothesis when value bounds must be
proved separately. `EnergySmooth` includes that additional value condition
and maps into this carrier by forgetting it.
-/
public import KsIndexLean.EnergySmooth

@[expose] public section


open Complex Real MeasureTheory Filter Topology
open scoped ContDiff

namespace KsIndex.FaithfulInjection

open KsIndex.Surface KsIndex.SurfaceForm KsIndex.GradOrtho

/-- **The gradient-energy carrier:** `EnergySmooth` minus the per-copy
value-`L²` condition. `IsSmooth` + finite Dirichlet (gradient) energy + the two representative
normalizations `PunctureZero`, `SeamVal`. -/
def GradEnergySmooth (k m : ℕ) : Submodule ℂ (ZMod (2 * m) → ℂ → ℂ) where
  carrier := {u | IsSmooth k m u ∧ (∀ n, IntegrableOn (gradSq (u n)) disk)
    ∧ PunctureZero k u ∧ SeamVal k u}
  zero_mem' := by
    refine ⟨isSmooth_zero k m, ?_, punctureZero_zero k m, seamVal_zero k m⟩
    intro n
    have h0 : gradSq ((0 : ZMod (2 * m) → ℂ → ℂ) n) = fun _ => (0 : ℝ) := by
      funext w; simp [gradSq]
    rw [h0]; exact integrableOn_zero
  add_mem' := fun {u v} hu hv =>
    ⟨isSmooth_add hu.1 hv.1,
     fun n => integrableOn_gradSq_add (fun w hw => differentiableAt_of_isSmooth hu.1 n hw)
       (fun w hw => differentiableAt_of_isSmooth hv.1 n hw) (hu.2.1 n) (hv.2.1 n),
     punctureZero_add hu.2.2.1 hv.2.2.1,
     seamVal_add hu.2.2.2 hv.2.2.2⟩
  smul_mem' := fun c u hu =>
    ⟨isSmooth_smul c hu.1,
     fun n => integrableOn_gradSq_smul c (fun w hw => differentiableAt_of_isSmooth hu.1 n hw)
       (hu.2.1 n),
     punctureZero_smul c hu.2.2.1,
     seamVal_smul c hu.2.2.2⟩

/-- `EnergySmooth` embeds in the weaker `GradEnergySmooth` (forget the value-`L²` condition) — so
any result proved for the `GradEnergySmooth` carrier applies a fortiori to `EnergySmooth`. -/
lemma energySmooth_le_gradEnergySmooth (k m : ℕ) :
    EnergySmooth k m ≤ GradEnergySmooth k m := by
  intro u hu
  exact ⟨hu.1, hu.2.1, hu.2.2.2.1, hu.2.2.2.2⟩

/-- Map an `EnergySmooth` member into `GradEnergySmooth` through
`energySmooth_le_gradEnergySmooth`, preserving its underlying function definitionally. -/
def esToGrad {k m : ℕ} (u : EnergySmooth k m) : GradEnergySmooth k m :=
  ⟨u.val, energySmooth_le_gradEnergySmooth k m u.property⟩

end KsIndex.FaithfulInjection
