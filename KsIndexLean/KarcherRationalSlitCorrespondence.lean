module

public import KsIndexLean.KarcherSlitIndex
public import KsIndexLean.KarcherSlitNullity

@[expose] public section


/-! Geometric index and nullity correspondence for rational quasiperiodic phases. -/
noncomputable section
namespace KsIndex.KarcherData.PaperHalfPeriodRealization
open KsIndex.Spectral KsIndex.FormIndex
variable [Fact (2 ≤ 3)] (R : PaperHalfPeriodRealization 3)

omit [Fact (2 ≤ 3)] in
lemma nonnegative_rational_phase (α : ℚ) (hα : 0 ≤ α) :
    (α.num.toNat : ℝ) / α.den = (α : ℝ) := by
  rw [Rat.cast_def]
  congr 1
  exact_mod_cast Int.toNat_of_nonneg (Rat.num_nonneg.mpr hα)

omit [Fact (2 ≤ 3)] in
lemma rational_phase_character (α : ℚ) (hα : 0 ≤ α) :
    zeta α.den ^ α.num.toNat = Spherical.paperPhase (α : ℝ) := by
  have h := paperRationalPhase_eq_zeta α.den α.num.toNat
  rw [nonnegative_rational_phase α hα] at h
  exact h.symm

/-- Index and nullity correspondence at every nonnegative rational phase, including the
paper’s range [0,1), with no exclusion of zero phase. The quotient uses the reduced denominator. -/
theorem rational_slit_index_nullity (α : ℚ) (hα : 0 ≤ α) (j : Fin 3) :
    letI : NeZero α.den := ⟨α.den_ne_zero⟩
    formIndex R.quotientJacobiQ
      (R.geometricSmoothJointSector (m := α.den) α.num.toNat j.val) =
      NegativeDensity.negativeIndex (fun u : paperSphericalPhaseCharacter (α : ℝ) j.val =>
        (Spherical.sphereChartJacobi (Trace.isOpen_boundaryArc 3 1)
          (WeakH1.surfacePotential 3) u.val.val u.val.val).re) ∧
    Module.finrank ℂ (R.geometricJointFiber (m := α.den) α.num.toNat j.val) =
      Module.finrank ℂ (paperSphericalCharacterRadical (α : ℝ) j.val
        (WeakH1.surfacePotential 3)) := by
  let : NeZero α.den := ⟨α.den_ne_zero⟩
  have hi := R.geometricSmoothJointSector_index_eq_sphere (m := α.den) α.num.toNat j.val
  have hn := R.geometricJointFiber_finrank_eq_sphere (m := α.den) α.num.toNat j.val
  rw [nonnegative_rational_phase α hα] at hi hn
  exact ⟨hi, hn⟩
end KsIndex.KarcherData.PaperHalfPeriodRealization
