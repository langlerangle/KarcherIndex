module

public import KsIndexLean.PaperSlitCharacterSpectrum
public import KsIndexLean.VariationalBracketing

@[expose] public section


noncomputable section
namespace KsIndex.Spectral
open KsIndex.Trace KsIndex.WeakH1 KsIndex.Spherical

lemma trial_bound_equiv {E F : Type*} [AddCommGroup E] [Module ℂ E]
    [AddCommGroup F] [Module ℂ F] (e : E ≃ₗ[ℂ] F)
    (Q M : E → ℝ) (R N : F → ℝ)
    (hQ : ∀ u, R (e u) = Q u) (hM : ∀ u, N (e u) = M u)
    (d : ℕ) (L : ℝ) :
    (∃ W : Submodule ℂ E, FiniteDimensional ℂ W ∧ Module.finrank ℂ W = d ∧
      ∀ u : W, Q u ≤ L * M u) ↔
    (∃ W : Submodule ℂ F, FiniteDimensional ℂ W ∧ Module.finrank ℂ W = d ∧
      ∀ u : W, R u ≤ L * N u) := by
  constructor
  · exact trial_bound_transport e.toLinearMap e.injective Q M R N hQ hM d L
  · apply trial_bound_transport e.symm.toLinearMap e.symm.injective R N Q M
    · intro u
      change Q (e.symm u) = R u
      simpa only [LinearEquiv.apply_symm_apply] using (hQ (e.symm u)).symm
    · intro u
      change M (e.symm u) = N u
      simpa only [LinearEquiv.apply_symm_apply] using (hM (e.symm u)).symm

lemma paperSlitCharacter_trial_bound_iff (α : ℝ) (j : ℕ)
    (V : BoundedRealPotential) (d : ℕ) (L : ℝ) :
    (∃ W : Submodule ℂ (finiteH1Domain (pairFiniteDomain (paperSlitCharacterDomain α j))),
      FiniteDimensional ℂ W ∧ Module.finrank ℂ W = d ∧ ∀ u : W,
        (finiteH1Jacobi _ V u.val u.val).re ≤
          L * ‖finiteH1WeightedValue (pairFiniteDomain (paperSlitCharacterDomain α j)) u.val‖ ^ 2) ↔
    (∃ W : Submodule ℂ (paperSphericalPhaseCharacter α j),
      FiniteDimensional ℂ W ∧ Module.finrank ℂ W = d ∧ ∀ u : W,
        (sphereChartJacobi (isOpen_boundaryArc 3 1) V u.val.val.val u.val.val.val).re ≤
          L * (paperSlitChartMass α u.val.val u.val.val).re) := by
  refine trial_bound_equiv (paperSlitCharacterSpectralCoordinates α j)
    (fun u => (finiteH1Jacobi _ V u u).re)
    (fun u => ‖finiteH1WeightedValue _ u‖ ^ 2)
    (fun u => (sphereChartJacobi (isOpen_boundaryArc 3 1) V u.val.val u.val.val).re)
    (fun u => (paperSlitChartMass α u.val u.val).re) ?_ ?_ d L
  · intro u
    rw [paperSlitCharacterSpectralCoordinates_jacobi]
  · intro u
    rw [paperSlitCharacterSpectralCoordinates_mass]
    exact inner_self_eq_norm_sq (𝕜 := ℂ) (finiteH1WeightedValue (pairFiniteDomain (paperSlitCharacterDomain α j)) u)

/-- Attained min-max on the actual spherical character domain, with its exact
Jacobi form and mass pairing; infinite spectral sectors. -/
lemma paperSphericalCharacter_infinite_minmax (α : ℝ) (j : ℕ)
    (V : BoundedRealPotential)
    [Infinite (finiteSpectralData (pairFiniteDomain (paperSlitCharacterDomain α j)) V).eigenbasisIndex]
    (n : ℕ) (L : ℝ) :
    (finiteSpectralData (pairFiniteDomain (paperSlitCharacterDomain α j)) V).infiniteReciprocalShift (V.C + 1) n ≤ L ↔
    ∃ W : Submodule ℂ (paperSphericalPhaseCharacter α j),
      FiniteDimensional ℂ W ∧ Module.finrank ℂ W = n + 1 ∧ ∀ u : W,
        (sphereChartJacobi (isOpen_boundaryArc 3 1) V u.val.val.val u.val.val.val).re ≤
          L * (paperSlitChartMass α u.val.val u.val.val).re :=
  (finiteCopyJacobi_infinite_minmax _ V n L).trans
    (paperSlitCharacter_trial_bound_iff α j V (n + 1) L)

/-- Finite sectors retain the bound that the chosen eigenvalue exists. -/
lemma paperSphericalCharacter_finite_minmax (α : ℝ) (j : ℕ)
    (V : BoundedRealPotential)
    [FiniteDimensional ℂ (WeightedFiniteAmbient (pairFiniteDomain (paperSlitCharacterDomain α j)))]
    (n : Fin (Module.finrank ℂ (WeightedFiniteAmbient (pairFiniteDomain (paperSlitCharacterDomain α j)))))
    (L : ℝ) :
    (finiteSpectralData (pairFiniteDomain (paperSlitCharacterDomain α j)) V).finiteReciprocalShift (V.C + 1) n ≤ L ↔
    ∃ W : Submodule ℂ (paperSphericalPhaseCharacter α j),
      FiniteDimensional ℂ W ∧ Module.finrank ℂ W = n.val + 1 ∧ ∀ u : W,
        (sphereChartJacobi (isOpen_boundaryArc 3 1) V u.val.val.val u.val.val.val).re ≤
          L * (paperSlitChartMass α u.val.val u.val.val).re :=
  (finiteCopyJacobi_finite_minmax _ V n L).trans
    (paperSlitCharacter_trial_bound_iff α j V (n.val + 1) L)

end KsIndex.Spectral
