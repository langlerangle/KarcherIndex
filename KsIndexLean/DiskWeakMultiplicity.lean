module

public import KsIndexLean.OrderedSpectralMultiplicity
public import KsIndexLean.SolutionEigenspaceTransport
public import KsIndexLean.JacobiSolutionEigenvalue

@[expose] public section


noncomputable section
namespace KsIndex.Spectral
open Module.End KsIndex.WeakH1 KsIndex.Spherical
variable (D : Submodule ℂ ComplexH1) [CompleteSpace D] (V : BoundedRealPotential)
local instance diskWeakMultiplicityInner : InnerProductSpace ℂ (D) := diskDomain_innerProductSpace D

/-- Weak eigenspace at unshifted level L, represented through the actual
weighted bulk embedding. Membership below identifies its full weak equation. -/
def diskWeakEigenspace (L : ℝ) : Submodule ℂ (D) :=
  solutionFormEigenspace (shiftedDiskForm D V) (shiftedDiskForm_coercive D V)
    (weightedDiskAmbientEmbedding D) (((L + (V.C + 1))⁻¹ : ℝ) : ℂ)

lemma mem_diskWeakEigenspace (L : ℝ) (hL : L + (V.C + 1) ≠ 0) (u : D) :
    u ∈ diskWeakEigenspace D V L ↔
      ∀ v : D, weakJacobi V u v = (L : ℂ) * inner ℂ (weightedDiskAmbientEmbedding D u) (weightedDiskAmbientEmbedding D v) := by
  change (weightedDiskAmbientEmbedding D u) ∈ eigenspace (diskSolutionOperator D V).toLinearMap
    (((L + (V.C + 1))⁻¹ : ℝ) : ℂ) ↔ _
  have h := diskSolutionOperator_eigen_iff D V u (L + (V.C + 1))⁻¹ (inv_ne_zero hL)
  exact mem_eigenspace_iff.trans (by simpa only [ContinuousLinearMap.coe_coe, inv_inv, add_sub_cancel_right] using h)

lemma diskWeakEigenspace_finrank (L : ℝ) (hL : L + (V.C + 1) ≠ 0) :
    Module.finrank ℂ (diskWeakEigenspace D V L) =
      Module.finrank ℂ (eigenspace (diskSolutionOperator D V).toLinearMap (((L + (V.C + 1))⁻¹ : ℝ) : ℂ)) :=
  solutionFormEigenspace_finrank (shiftedDiskForm D V) (shiftedDiskForm_coercive D V)
    (weightedDiskAmbientEmbedding D) (weightedDiskAmbientEmbedding_spec D).1 _
    (Complex.ofReal_ne_zero.mpr (inv_ne_zero hL))

lemma diskWeakEigenspace_infinite_count
    [Infinite (diskSpectralData D V).eigenbasisIndex] (L : ℝ) (hL : L + (V.C + 1) ≠ 0) :
    Module.finrank ℂ (diskWeakEigenspace D V L) =
      weakSpectralCount ((diskSpectralData D V).infiniteReciprocalShift (V.C + 1))
        ((diskSpectralData D V).infiniteReciprocalShift_tendsto_atTop (V.C + 1)) L -
      strictSpectralCount ((diskSpectralData D V).infiniteReciprocalShift (V.C + 1))
        ((diskSpectralData D V).infiniteReciprocalShift_tendsto_atTop (V.C + 1)) L := by
  rw [diskWeakEigenspace_finrank D V L hL]
  exact (diskSpectralData D V).infinite_level_multiplicity (V.C + 1) L

lemma diskWeakEigenspace_finite_count
    [FiniteDimensional ℂ (WeightedDiskAmbient D)] (L : ℝ) (hL : L + (V.C + 1) ≠ 0) :
    Module.finrank ℂ (diskWeakEigenspace D V L) =
      (diskSpectralData D V).finiteWeakCount (V.C + 1) L -
      (diskSpectralData D V).finiteStrictCount (V.C + 1) L := by
  rw [diskWeakEigenspace_finrank D V L hL]
  exact (diskSpectralData D V).finite_level_multiplicity (V.C + 1) L


lemma diskWeakEigenspace_exceptional (L : ℝ) (hL : L + (V.C + 1) = 0) :
    diskWeakEigenspace D V L = ⊥ := by
  change (eigenspace (diskSpectralData D V).operator.toLinearMap
    (((L + (V.C + 1))⁻¹ : ℝ) : ℂ)).comap (weightedDiskAmbientEmbedding D).toLinearMap = ⊥
  have hz : eigenspace (diskSpectralData D V).operator.toLinearMap
      (((L + (V.C + 1))⁻¹ : ℝ) : ℂ) = ⊥ := by
    simpa only [hL, inv_zero, Complex.ofReal_zero] using (diskSpectralData D V).zero_eigenspace
  exact (congrArg (fun W : Submodule ℂ (WeightedDiskAmbient D) =>
    W.comap (weightedDiskAmbientEmbedding D).toLinearMap) hz).trans
      ((Submodule.comap_bot _).trans (LinearMap.ker_eq_bot.mpr (weightedDiskAmbientEmbedding_spec D).1))

omit [CompleteSpace (D)] in
lemma diskWeakEquation_exceptional (L : ℝ) (hL : L + (V.C + 1) = 0)
    (u : D) (hu : ∀ v : D, weakJacobi V u v =
      (L : ℂ) * inner ℂ (weightedDiskAmbientEmbedding D u) (weightedDiskAmbientEmbedding D v)) : u = 0 := by
  have hc : (L : ℂ) + ((V.C : ℂ) + 1) = 0 := by exact_mod_cast hL
  have hs := shiftedDiskForm_apply D V u u
  have hb : (shiftedDiskForm D V) u u = 0 := by
    calc
      _ = weakJacobi V u u + ((V.C : ℂ) + 1) * inner ℂ (weightedDiskAmbientEmbedding D u) (weightedDiskAmbientEmbedding D u) := hs
      _ = (L : ℂ) * inner ℂ (weightedDiskAmbientEmbedding D u) (weightedDiskAmbientEmbedding D u) +
          ((V.C : ℂ) + 1) * inner ℂ (weightedDiskAmbientEmbedding D u) (weightedDiskAmbientEmbedding D u) :=
        congrArg (fun z => z + ((V.C : ℂ) + 1) * inner ℂ (weightedDiskAmbientEmbedding D u) (weightedDiskAmbientEmbedding D u)) (hu u)
      _ = 0 := by linear_combination hc * inner ℂ (weightedDiskAmbientEmbedding D u) (weightedDiskAmbientEmbedding D u)
  have hn : ‖u‖ ^ 2 ≤ 0 := ((shiftedDiskForm_coercive D V) u).trans_eq (congrArg Complex.re hb)
  exact norm_eq_zero.mp (by nlinarith [norm_nonneg u])

lemma mem_diskWeakEigenspace_all (L : ℝ) (u : D) :
    u ∈ diskWeakEigenspace D V L ↔ ∀ v : D, weakJacobi V u v =
      (L : ℂ) * inner ℂ (weightedDiskAmbientEmbedding D u) (weightedDiskAmbientEmbedding D v) := by
  by_cases hL : L + (V.C + 1) = 0
  · have hp := congrArg (fun W : Submodule ℂ (D) => u ∈ W)
      (diskWeakEigenspace_exceptional D V L hL)
    refine (Iff.of_eq hp).trans ?_
    change u = 0 ↔ _
    constructor
    · rintro rfl v
      change (domainJacobiForm D V) 0 v = (L : ℂ) * inner ℂ ((weightedDiskAmbientEmbedding D) 0) ((weightedDiskAmbientEmbedding D) v)
      have hz := congrArg (fun f : D →L[ℂ] ℂ => f v) ((domainJacobiForm D V).toLinearMap.map_zero)
      exact hz.trans (by simp only [zero_apply,(weightedDiskAmbientEmbedding D).map_zero, inner_zero_left, mul_zero])
    · exact diskWeakEquation_exceptional D V L hL u
  · exact mem_diskWeakEigenspace D V L hL u


lemma diskWeakEigenspace_finrank_all (L : ℝ) :
    Module.finrank ℂ (diskWeakEigenspace D V L) =
      Module.finrank ℂ (eigenspace (diskSpectralData D V).operator.toLinearMap
        (((L + (V.C + 1))⁻¹ : ℝ) : ℂ)) := by
  by_cases hL : L + (V.C + 1) = 0
  · have hz : eigenspace (diskSpectralData D V).operator.toLinearMap
        (((L + (V.C + 1))⁻¹ : ℝ) : ℂ) = ⊥ := by
      simpa only [hL, inv_zero, Complex.ofReal_zero] using (diskSpectralData D V).zero_eigenspace
    have hleft := congrArg (fun W : Submodule ℂ (D) => Module.finrank ℂ W)
      (diskWeakEigenspace_exceptional D V L hL)
    have hright := congrArg (fun W : Submodule ℂ (WeightedDiskAmbient D) => Module.finrank ℂ W) hz
    simp only [finrank_bot] at hleft hright
    exact hleft.trans hright.symm
  · exact diskWeakEigenspace_finrank D V L hL

lemma diskWeakEigenspace_finiteDimensional (L : ℝ) :
    FiniteDimensional ℂ (diskWeakEigenspace D V L) := by
  by_cases hL : L + (V.C + 1) = 0
  · rw [diskWeakEigenspace_exceptional D V L hL]
    infer_instance
  · exact solutionFormEigenspace_finiteDimensional (shiftedDiskForm D V) (shiftedDiskForm_coercive D V)
      (weightedDiskAmbientEmbedding D) (weightedDiskAmbientEmbedding_spec D).1 (weightedDiskAmbientEmbedding_spec D).2.2 _
      (Complex.ofReal_ne_zero.mpr (inv_ne_zero hL))

lemma diskWeakEigenspace_infinite_count_all
    [Infinite (diskSpectralData D V).eigenbasisIndex] (L : ℝ) :
    Module.finrank ℂ (diskWeakEigenspace D V L) =
      weakSpectralCount ((diskSpectralData D V).infiniteReciprocalShift (V.C + 1))
        ((diskSpectralData D V).infiniteReciprocalShift_tendsto_atTop (V.C + 1)) L -
      strictSpectralCount ((diskSpectralData D V).infiniteReciprocalShift (V.C + 1))
        ((diskSpectralData D V).infiniteReciprocalShift_tendsto_atTop (V.C + 1)) L :=
  (diskWeakEigenspace_finrank_all D V L).trans
    ((diskSpectralData D V).infinite_level_multiplicity (V.C + 1) L)

lemma diskWeakEigenspace_finite_count_all
    [FiniteDimensional ℂ (WeightedDiskAmbient D)] (L : ℝ) :
    Module.finrank ℂ (diskWeakEigenspace D V L) =
      (diskSpectralData D V).finiteWeakCount (V.C + 1) L -
      (diskSpectralData D V).finiteStrictCount (V.C + 1) L :=
  (diskWeakEigenspace_finrank_all D V L).trans
    ((diskSpectralData D V).finite_level_multiplicity (V.C + 1) L)

end KsIndex.Spectral
