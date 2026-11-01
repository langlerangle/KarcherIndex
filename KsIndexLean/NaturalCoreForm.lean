module

public import KsIndexLean.NaturalCoreCharacter
public import KsIndexLean.WeakH1Integration
public import KsIndexLean.WeakDiskChain

@[expose] public section


open Set MeasureTheory

noncomputable section
namespace KsIndex.Trace
open KsIndex.WeakH1 KsIndex.SingleDisk

/-- The adopted weak disk form agrees with the existing geometric-density disk form. -/
lemma smooth_weakJacobi_self_eq_Qd {k : ℕ} (hk : 2 ≤ k) (F : SmoothH1Data) :
    weakJacobi (surfacePotential k) (smoothToH1 F) (smoothToH1 F) =
      (KsIndex.SingleDiskBridge.Qd k F.F : ℂ) := by
  rw [smooth_weakJacobi_eq_classical]
  change (∫ w in (disk : Set ℂ), KsIndex.GradOrtho.gradInner F.F F.F w) -
    (∫ w in (disk : Set ℂ), (Surface.potV k w : ℂ) * (starRingEnd ℂ) (F.F w) * F.F w) = _
  rw [KsIndex.SingleDiskBridge.Qd, Surface.dirichletG_sub_potentialG hk, Complex.ofReal_sub]
  have e1 : ∫ w in (disk : Set ℂ), (Surface.gradSq F.F w : ℂ) =
      ((∫ w in (disk : Set ℂ), Surface.gradSq F.F w : ℝ) : ℂ) := integral_ofReal
  have e2 : ∫ w in (disk : Set ℂ), ((Surface.potV k w * ‖F.F w‖ ^ 2 : ℝ) : ℂ) =
      ((∫ w in (disk : Set ℂ), Surface.potV k w * ‖F.F w‖ ^ 2 : ℝ) : ℂ) := integral_ofReal
  change _ = ((∫ w in (disk : Set ℂ), Surface.gradSq F.F w : ℝ) : ℂ) -
    ((∫ w in (disk : Set ℂ), Surface.potV k w * ‖F.F w‖ ^ 2 : ℝ) : ℂ)
  rw [← e1, ← e2]
  congr 1
  · exact integral_congr_ae
      (Filter.Eventually.of_forall fun w => KsIndex.GradOrtho.gradInner_self F.F w)
  · refine integral_congr_ae (Filter.Eventually.of_forall fun w => ?_)
    push_cast
    rw [mul_assoc, Complex.conj_mul']

lemma naturalCoreToMixed_form {k : ℕ} (hk : 2 ≤ k) (b1 b0 : Bool) (f : NatCc k b1 b0) :
    weakJacobi (surfacePotential k) (naturalCoreToMixed (by omega) b1 b0 f).val
      (naturalCoreToMixed (by omega) b1 b0 f).val =
      (KsIndex.SingleDiskBridge.Qd k f.val : ℂ) :=
  smooth_weakJacobi_self_eq_Qd hk (naturalCoreData (by omega) f)

/-- The seam-constrained realization is the already adopted diskwise adapter. -/
lemma energySmoothCopy_eq_adopted {k m : ℕ} (u : KsIndex.FaithfulInjection.EnergySmooth k m)
    (n : ZMod (2 * m)) : energySmoothCopy u n = energySmoothToH1 u n := rfl

/-- The chain map preserves the existing polarized surface Jacobi form. -/
lemma energySmoothToWeakChain_form {k m : ℕ} [NeZero m]
    (u v : KsIndex.FaithfulInjection.EnergySmooth k m) :
    ∑ n : ZMod (2 * m), weakJacobi (surfacePotential k)
      ((energySmoothToWeakChain k m u).val n) ((energySmoothToWeakChain k m v).val n) =
      SurfaceForm.jacobiB k m u.val v.val :=
  sum_weakJacobi_eq_jacobiB u v

end KsIndex.Trace
