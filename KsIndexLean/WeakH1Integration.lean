module

/-
The diskwise Sobolev realization of EnergySmooth and its polarized Jacobi form.
This bridge does not identify the full surface H¹ domain or construct seam traces.
-/
public import KsIndexLean.WeakH1Adapter
public import KsIndexLean.EnergySmooth

@[expose] public section


noncomputable section
open Complex MeasureTheory
open scoped ContDiff

namespace KsIndex.WeakH1

/-- The actual potential, with its proven uniform bound on the open disk. -/
def surfacePotential (k : ℕ) : BoundedRealPotential where
  V := Surface.potV k
  C := 8 * ((k : ℝ) - 1) ^ 2
  nonneg := by positivity
  measurable := (SurfaceForm.continuous_potV k).measurable.aestronglyMeasurable
  bound := by
    refine ae_restrict_of_forall_mem disk.isOpen.measurableSet fun w hw => ?_
    rw [abs_of_nonneg (SurfaceForm.potV_nonneg k w)]
    exact SurfaceForm.potV_le (le_of_lt (SurfaceForm.mem_disk_iff.mp hw))

/-- Each derivative coordinate is square integrable by the actual Dirichlet bound. -/
lemma coordinate_memLp {f : ℂ → ℂ}
    (hf : IntegrableOn (Surface.gradSq f) Surface.disk) :
    MemLp (fun w => fderiv ℝ f w 1) 2 (volume.restrict (disk : Set ℂ)) ∧
    MemLp (fun w => fderiv ℝ f w I) 2 (volume.restrict (disk : Set ℂ)) := by
  constructor
  · apply (memLp_two_iff_integrable_sq_norm
      (measurable_fderiv_apply_const ℝ f 1).aestronglyMeasurable).2
    refine hf.mono'
      (((measurable_fderiv_apply_const ℝ f 1).norm).pow_const 2).aestronglyMeasurable ?_
    filter_upwards with w
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    exact le_add_of_nonneg_right (sq_nonneg _)
  · apply (memLp_two_iff_integrable_sq_norm
      (measurable_fderiv_apply_const ℝ f I).aestronglyMeasurable).2
    refine hf.mono'
      (((measurable_fderiv_apply_const ℝ f I).norm).pow_const 2).aestronglyMeasurable ?_
    filter_upwards with w
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    exact le_add_of_nonneg_left (sq_nonneg _)

/-- Interior smoothness and both energy conditions supply every adapter hypothesis. -/
def energySmoothData {k m : ℕ} (u : FaithfulInjection.EnergySmooth k m)
    (n : ZMod (2 * m)) : SmoothH1Data where
  F := u.val n
  smooth := u.property.1.1 n
  value_mem := (memLp_two_iff_integrable_sq_norm
    ((u.property.1.1 n).continuousOn.aestronglyMeasurable disk.isOpen.measurableSet)).2
      (u.property.2.2.1 n)
  dx_mem := (coordinate_memLp (u.property.2.1 n)).1
  dy_mem := (coordinate_memLp (u.property.2.1 n)).2

/-- The diskwise weak carrier realized by an EnergySmooth field. -/
def energySmoothToH1 {k m : ℕ} (u : FaithfulInjection.EnergySmooth k m)
    (n : ZMod (2 * m)) : ComplexH1 := smoothToH1 (energySmoothData u n)

/-- Actual main form agreement, summed over all half-period copies. -/
theorem sum_weakJacobi_eq_jacobiB {k m : ℕ} [NeZero m]
    (u v : FaithfulInjection.EnergySmooth k m) :
    letI : NeZero (2 * m) := ⟨by have := NeZero.ne m; omega⟩
    ∑ n : ZMod (2 * m), weakJacobi (surfacePotential k)
      (energySmoothToH1 u n) (energySmoothToH1 v n) =
      SurfaceForm.jacobiB k m u.val v.val := by
  unfold SurfaceForm.jacobiB
  apply Finset.sum_congr rfl
  intro n _
  exact smooth_weakJacobi_eq_classical (surfacePotential k)
    (energySmoothData u n) (energySmoothData v n)

/-- The diagonal specializes to the repository's real Jacobi quadratic form. -/
theorem sum_weakJacobi_self_eq_jacobiQ {k m : ℕ} [NeZero m] (hk : 2 ≤ k)
    (u : FaithfulInjection.EnergySmooth k m) :
    letI : NeZero (2 * m) := ⟨by have := NeZero.ne m; omega⟩
    ∑ n : ZMod (2 * m), weakJacobi (surfacePotential k)
      (energySmoothToH1 u n) (energySmoothToH1 u n) =
      (Surface.jacobiQ k m u.val : ℂ) := by
  rw [sum_weakJacobi_eq_jacobiB, SurfaceForm.jacobiB_self hk]

end KsIndex.WeakH1
