module

public import KsIndexLean.OrderedSpectralMultiplicity
public import KsIndexLean.SolutionEigenspaceTransport
public import KsIndexLean.JacobiSolutionEigenvalue

@[expose] public section


noncomputable section
namespace KsIndex.Spectral
open Module.End KsIndex.WeakH1 KsIndex.Spherical
variable {ι : Type*} [Fintype ι] (D : Submodule ℂ (ι → ComplexH1)) [CompleteSpace (finiteH1Domain D)] (V : BoundedRealPotential)
local instance finiteCopyWeakMultiplicityInner : InnerProductSpace ℂ (finiteH1Domain D) := finiteH1Domain_innerProductSpace D

/-- Weak eigenspace at unshifted level L, represented through the actual
weighted bulk embedding. Membership below identifies its full weak equation. -/
def finiteCopyWeakEigenspace (L : ℝ) : Submodule ℂ (finiteH1Domain D) :=
  solutionFormEigenspace (shiftedFiniteForm D V) (shiftedFiniteForm_coercive D V)
    (finiteH1WeightedValue D) (((L + (V.C + 1))⁻¹ : ℝ) : ℂ)

lemma mem_finiteCopyWeakEigenspace (L : ℝ) (hL : L + (V.C + 1) ≠ 0) (u : finiteH1Domain D) :
    u ∈ finiteCopyWeakEigenspace D V L ↔
      ∀ v : finiteH1Domain D, finiteH1Jacobi D V u v = (L : ℂ) * inner ℂ (finiteH1WeightedValue D u) (finiteH1WeightedValue D v) := by
  change (finiteH1WeightedValue D u) ∈ eigenspace (finiteSolutionOperator D V).toLinearMap
    (((L + (V.C + 1))⁻¹ : ℝ) : ℂ) ↔ _
  have h := finiteSolutionOperator_eigen_iff D V u (L + (V.C + 1))⁻¹ (inv_ne_zero hL)
  exact mem_eigenspace_iff.trans (by simpa only [ContinuousLinearMap.coe_coe, inv_inv, add_sub_cancel_right] using h)

lemma finiteCopyWeakEigenspace_finrank (L : ℝ) (hL : L + (V.C + 1) ≠ 0) :
    Module.finrank ℂ (finiteCopyWeakEigenspace D V L) =
      Module.finrank ℂ (eigenspace (finiteSolutionOperator D V).toLinearMap (((L + (V.C + 1))⁻¹ : ℝ) : ℂ)) :=
  solutionFormEigenspace_finrank (shiftedFiniteForm D V) (shiftedFiniteForm_coercive D V)
    (finiteH1WeightedValue D) (finiteH1WeightedValue_spec D).1 _
    (Complex.ofReal_ne_zero.mpr (inv_ne_zero hL))

lemma finiteCopyWeakEigenspace_infinite_count
    [Infinite (finiteSpectralData D V).eigenbasisIndex] (L : ℝ) (hL : L + (V.C + 1) ≠ 0) :
    Module.finrank ℂ (finiteCopyWeakEigenspace D V L) =
      weakSpectralCount ((finiteSpectralData D V).infiniteReciprocalShift (V.C + 1))
        ((finiteSpectralData D V).infiniteReciprocalShift_tendsto_atTop (V.C + 1)) L -
      strictSpectralCount ((finiteSpectralData D V).infiniteReciprocalShift (V.C + 1))
        ((finiteSpectralData D V).infiniteReciprocalShift_tendsto_atTop (V.C + 1)) L := by
  rw [finiteCopyWeakEigenspace_finrank D V L hL]
  exact (finiteSpectralData D V).infinite_level_multiplicity (V.C + 1) L

lemma finiteCopyWeakEigenspace_finite_count
    [FiniteDimensional ℂ (WeightedFiniteAmbient D)] (L : ℝ) (hL : L + (V.C + 1) ≠ 0) :
    Module.finrank ℂ (finiteCopyWeakEigenspace D V L) =
      (finiteSpectralData D V).finiteWeakCount (V.C + 1) L -
      (finiteSpectralData D V).finiteStrictCount (V.C + 1) L := by
  rw [finiteCopyWeakEigenspace_finrank D V L hL]
  exact (finiteSpectralData D V).finite_level_multiplicity (V.C + 1) L


lemma finiteCopyWeakEigenspace_exceptional (L : ℝ) (hL : L + (V.C + 1) = 0) :
    finiteCopyWeakEigenspace D V L = ⊥ := by
  change (eigenspace (finiteSpectralData D V).operator.toLinearMap
    (((L + (V.C + 1))⁻¹ : ℝ) : ℂ)).comap (finiteH1WeightedValue D).toLinearMap = ⊥
  have hz : eigenspace (finiteSpectralData D V).operator.toLinearMap
      (((L + (V.C + 1))⁻¹ : ℝ) : ℂ) = ⊥ := by
    simpa only [hL, inv_zero, Complex.ofReal_zero] using (finiteSpectralData D V).zero_eigenspace
  exact (congrArg (fun W : Submodule ℂ (WeightedFiniteAmbient D) =>
    W.comap (finiteH1WeightedValue D).toLinearMap) hz).trans
      ((Submodule.comap_bot _).trans (LinearMap.ker_eq_bot.mpr (finiteH1WeightedValue_spec D).1))

omit [CompleteSpace (finiteH1Domain D)] in
lemma finiteCopyWeakEquation_exceptional (L : ℝ) (hL : L + (V.C + 1) = 0)
    (u : finiteH1Domain D) (hu : ∀ v : finiteH1Domain D, finiteH1Jacobi D V u v =
      (L : ℂ) * inner ℂ (finiteH1WeightedValue D u) (finiteH1WeightedValue D v)) : u = 0 := by
  have hc : (L : ℂ) + ((V.C : ℂ) + 1) = 0 := by exact_mod_cast hL
  have hs := shiftedFiniteForm_apply D V u u
  have hb : (shiftedFiniteForm D V) u u = 0 := by
    calc
      _ = finiteH1Jacobi D V u u + ((V.C : ℂ) + 1) * inner ℂ (finiteH1WeightedValue D u) (finiteH1WeightedValue D u) := hs
      _ = (L : ℂ) * inner ℂ (finiteH1WeightedValue D u) (finiteH1WeightedValue D u) +
          ((V.C : ℂ) + 1) * inner ℂ (finiteH1WeightedValue D u) (finiteH1WeightedValue D u) :=
        congrArg (fun z => z + ((V.C : ℂ) + 1) * inner ℂ (finiteH1WeightedValue D u) (finiteH1WeightedValue D u)) (hu u)
      _ = 0 := by linear_combination hc * inner ℂ (finiteH1WeightedValue D u) (finiteH1WeightedValue D u)
  have hn : ‖u‖ ^ 2 ≤ 0 := ((shiftedFiniteForm_coercive D V) u).trans_eq (congrArg Complex.re hb)
  exact norm_eq_zero.mp (by nlinarith [norm_nonneg u])

lemma mem_finiteCopyWeakEigenspace_all (L : ℝ) (u : finiteH1Domain D) :
    u ∈ finiteCopyWeakEigenspace D V L ↔ ∀ v : finiteH1Domain D, finiteH1Jacobi D V u v =
      (L : ℂ) * inner ℂ (finiteH1WeightedValue D u) (finiteH1WeightedValue D v) := by
  by_cases hL : L + (V.C + 1) = 0
  · have hp := congrArg (fun W : Submodule ℂ (finiteH1Domain D) => u ∈ W)
      (finiteCopyWeakEigenspace_exceptional D V L hL)
    refine (Iff.of_eq hp).trans ?_
    change u = 0 ↔ _
    constructor
    · rintro rfl v
      have hz := congrArg (fun f : finiteH1Domain D →L[ℂ] ℂ => f v) ((finiteJacobiForm D V).toLinearMap.map_zero)
      exact (finiteJacobiForm_apply D V 0 v).symm.trans
        (hz.trans (by simp only [zero_apply,(finiteH1WeightedValue D).map_zero, inner_zero_left, mul_zero]))
    · exact finiteCopyWeakEquation_exceptional D V L hL u
  · exact mem_finiteCopyWeakEigenspace D V L hL u


lemma finiteCopyWeakEigenspace_finrank_all (L : ℝ) :
    Module.finrank ℂ (finiteCopyWeakEigenspace D V L) =
      Module.finrank ℂ (eigenspace (finiteSpectralData D V).operator.toLinearMap
        (((L + (V.C + 1))⁻¹ : ℝ) : ℂ)) := by
  by_cases hL : L + (V.C + 1) = 0
  · have hz : eigenspace (finiteSpectralData D V).operator.toLinearMap
        (((L + (V.C + 1))⁻¹ : ℝ) : ℂ) = ⊥ := by
      simpa only [hL, inv_zero, Complex.ofReal_zero] using (finiteSpectralData D V).zero_eigenspace
    have hleft := congrArg (fun W : Submodule ℂ (finiteH1Domain D) => Module.finrank ℂ W)
      (finiteCopyWeakEigenspace_exceptional D V L hL)
    have hright := congrArg (fun W : Submodule ℂ (WeightedFiniteAmbient D) => Module.finrank ℂ W) hz
    simp only [finrank_bot] at hleft hright
    exact hleft.trans hright.symm
  · exact finiteCopyWeakEigenspace_finrank D V L hL

lemma finiteCopyWeakEigenspace_finiteDimensional (L : ℝ) :
    FiniteDimensional ℂ (finiteCopyWeakEigenspace D V L) := by
  by_cases hL : L + (V.C + 1) = 0
  · rw [finiteCopyWeakEigenspace_exceptional D V L hL]
    infer_instance
  · exact solutionFormEigenspace_finiteDimensional (shiftedFiniteForm D V) (shiftedFiniteForm_coercive D V)
      (finiteH1WeightedValue D) (finiteH1WeightedValue_spec D).1 (finiteH1WeightedValue_spec D).2.2 _
      (Complex.ofReal_ne_zero.mpr (inv_ne_zero hL))

lemma finiteCopyWeakEigenspace_infinite_count_all
    [Infinite (finiteSpectralData D V).eigenbasisIndex] (L : ℝ) :
    Module.finrank ℂ (finiteCopyWeakEigenspace D V L) =
      weakSpectralCount ((finiteSpectralData D V).infiniteReciprocalShift (V.C + 1))
        ((finiteSpectralData D V).infiniteReciprocalShift_tendsto_atTop (V.C + 1)) L -
      strictSpectralCount ((finiteSpectralData D V).infiniteReciprocalShift (V.C + 1))
        ((finiteSpectralData D V).infiniteReciprocalShift_tendsto_atTop (V.C + 1)) L :=
  (finiteCopyWeakEigenspace_finrank_all D V L).trans
    ((finiteSpectralData D V).infinite_level_multiplicity (V.C + 1) L)

lemma finiteCopyWeakEigenspace_finite_count_all
    [FiniteDimensional ℂ (WeightedFiniteAmbient D)] (L : ℝ) :
    Module.finrank ℂ (finiteCopyWeakEigenspace D V L) =
      (finiteSpectralData D V).finiteWeakCount (V.C + 1) L -
      (finiteSpectralData D V).finiteStrictCount (V.C + 1) L :=
  (finiteCopyWeakEigenspace_finrank_all D V L).trans
    ((finiteSpectralData D V).finite_level_multiplicity (V.C + 1) L)

end KsIndex.Spectral
