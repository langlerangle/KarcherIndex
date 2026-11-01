module

/-
# Smooth finite-energy representatives and their tested Jacobi kernel

`EnergySmooth k m` is a complex submodule of pointwise copy fields. Its
conditions are `IsSmooth`, finite flat Dirichlet energy, finite squared-norm
integral, and the representative normalizations `PunctureZero` and `SeamVal`.
Interior smoothness supplies the differentiability needed for derivative
additivity and scalar multiplication, so these conditions are closed under
the submodule operations.

The integral estimates establish additivity and conjugate-linearity in the
first slot of `jacobiB` against `CcSmooth` tests. `WeakKer` consists of the
members of `EnergySmooth` that annihilate every such test. These definitions
use smooth pointwise representatives; they do not define a weak-gradient
Sobolev quotient. Comparison with a radical tested on a larger domain requires
separate density and continuity results.
-/
public import KsIndexLean.SurfaceForm

@[expose] public section


open Complex Real MeasureTheory Filter Topology
open scoped ContDiff

namespace KsIndex.FaithfulInjection

open KsIndex.Surface KsIndex.SurfaceForm KsIndex.GradOrtho

variable {k m : ℕ}

/-- `IsSmooth` supplies differentiability at every point of the open disk. -/
lemma differentiableAt_of_isSmooth {u : ZMod (2 * m) → ℂ → ℂ} (hu : IsSmooth k m u)
    (n : ZMod (2 * m)) {w : ℂ} (hw : w ∈ disk) : DifferentiableAt ℝ (u n) w :=
  ((hu.1 n).contDiffAt (Metric.isOpen_ball.mem_nhds hw)).differentiableAt (by simp)

/-- `gradSq` is a sum of squares, hence nonnegative. -/
lemma gradSq_nonneg (f : ℂ → ℂ) (w : ℂ) : 0 ≤ gradSq f w := by
  unfold gradSq; positivity

/-- `gradSq f` is measurable for any `f` (`fderiv` is measurable even off the differentiability
set), so no regularity is needed for the measurability half of integrability. -/
lemma measurable_gradSq (f : ℂ → ℂ) : Measurable (gradSq f) := by
  unfold gradSq
  exact (((measurable_fderiv_apply_const ℝ f 1).norm).pow_const 2).add
    (((measurable_fderiv_apply_const ℝ f I).norm).pow_const 2)

/-- Factor-`2` subadditivity of `gradSq` where both summands are differentiable. -/
lemma gradSq_add_le {f g : ℂ → ℂ} {w : ℂ}
    (hf : DifferentiableAt ℝ f w) (hg : DifferentiableAt ℝ g w) :
    gradSq (f + g) w ≤ 2 * gradSq f w + 2 * gradSq g w := by
  have hfg : fderiv ℝ (f + g) w = fderiv ℝ f w + fderiv ℝ g w := fderiv_add hf hg
  have key : ∀ z : ℂ, ‖(fderiv ℝ (f + g) w) z‖ ^ 2
      ≤ 2 * ‖fderiv ℝ f w z‖ ^ 2 + 2 * ‖fderiv ℝ g w z‖ ^ 2 := by
    intro z
    rw [hfg]
    have hle : ‖(fderiv ℝ f w) z + (fderiv ℝ g w) z‖
        ≤ ‖(fderiv ℝ f w) z‖ + ‖(fderiv ℝ g w) z‖ := norm_add_le _ _
    have h2 : ‖(fderiv ℝ f w) z + (fderiv ℝ g w) z‖ ^ 2
        ≤ (‖(fderiv ℝ f w) z‖ + ‖(fderiv ℝ g w) z‖) ^ 2 := by gcongr
    have h3 : (‖(fderiv ℝ f w) z‖ + ‖(fderiv ℝ g w) z‖) ^ 2
        ≤ 2 * ‖fderiv ℝ f w z‖ ^ 2 + 2 * ‖fderiv ℝ g w z‖ ^ 2 := by
      nlinarith [sq_nonneg (‖(fderiv ℝ f w) z‖ - ‖(fderiv ℝ g w) z‖)]
    exact h2.trans h3
  have h1 := key 1
  have hI := key I
  unfold gradSq
  linarith

/-- `gradSq` scales by `‖c‖²` under scalar multiplication (at a differentiability point). -/
lemma gradSq_smul_of_diff (c : ℂ) {f : ℂ → ℂ} {w : ℂ} (hf : DifferentiableAt ℝ f w) :
    gradSq (c • f) w = ‖c‖ ^ 2 * gradSq f w := by
  have hfd : fderiv ℝ (c • f) w = c • fderiv ℝ f w := fderiv_const_smul hf c
  unfold gradSq
  rw [hfd]
  have e1 : ‖(c • fderiv ℝ f w) (1 : ℂ)‖ = ‖c‖ * ‖(fderiv ℝ f w) 1‖ := by
    rw [show (c • fderiv ℝ f w) (1 : ℂ) = c • ((fderiv ℝ f w) 1) from rfl, norm_smul]
  have eI : ‖(c • fderiv ℝ f w) I‖ = ‖c‖ * ‖(fderiv ℝ f w) I‖ := by
    rw [show (c • fderiv ℝ f w) I = c • ((fderiv ℝ f w) I) from rfl, norm_smul]
  rw [e1, eI]; ring

/-- Finite Dirichlet energy is preserved under sums of interior-differentiable fields. -/
lemma integrableOn_gradSq_add {f g : ℂ → ℂ}
    (hf : ∀ w ∈ disk, DifferentiableAt ℝ f w) (hg : ∀ w ∈ disk, DifferentiableAt ℝ g w)
    (hfi : IntegrableOn (gradSq f) disk) (hgi : IntegrableOn (gradSq g) disk) :
    IntegrableOn (gradSq (f + g)) disk := by
  have hbound : IntegrableOn (fun w => 2 * gradSq f w + 2 * gradSq g w) disk :=
    (hfi.const_mul 2).add (hgi.const_mul 2)
  refine hbound.mono' (measurable_gradSq _).aestronglyMeasurable ?_
  refine ae_restrict_of_forall_mem measurableSet_disk fun w hw => ?_
  rw [Real.norm_of_nonneg (gradSq_nonneg _ _)]
  exact gradSq_add_le (hf w hw) (hg w hw)

/-- Finite Dirichlet energy is preserved under scalar multiplication. -/
lemma integrableOn_gradSq_smul (c : ℂ) {f : ℂ → ℂ}
    (hf : ∀ w ∈ disk, DifferentiableAt ℝ f w) (hfi : IntegrableOn (gradSq f) disk) :
    IntegrableOn (gradSq (c • f)) disk := by
  have hbound : IntegrableOn (fun w => ‖c‖ ^ 2 * gradSq f w) disk := hfi.const_mul _
  refine hbound.mono' (measurable_gradSq _).aestronglyMeasurable ?_
  refine ae_restrict_of_forall_mem measurableSet_disk fun w hw => ?_
  rw [Real.norm_of_nonneg (gradSq_nonneg _ _)]
  exact le_of_eq (gradSq_smul_of_diff c (hf w hw))

/-- Finite `L²` energy is preserved under sums of fields continuous on the disk. -/
lemma integrableOn_normSq_add {f g : ℂ → ℂ}
    (hf : ContinuousOn f disk) (hg : ContinuousOn g disk)
    (hfi : IntegrableOn (fun w => ‖f w‖ ^ 2) disk) (hgi : IntegrableOn (fun w => ‖g w‖ ^ 2) disk) :
    IntegrableOn (fun w => ‖(f + g) w‖ ^ 2) disk := by
  have hbound : IntegrableOn (fun w => 2 * ‖f w‖ ^ 2 + 2 * ‖g w‖ ^ 2) disk :=
    (hfi.const_mul 2).add (hgi.const_mul 2)
  have hmeas : AEStronglyMeasurable (fun w => ‖(f + g) w‖ ^ 2) (volume.restrict disk) :=
    (((hf.add hg).norm).pow 2).aestronglyMeasurable measurableSet_disk
  refine hbound.mono' hmeas ?_
  refine ae_restrict_of_forall_mem measurableSet_disk fun w _ => ?_
  rw [Real.norm_of_nonneg (by positivity)]
  have hfgw : (f + g) w = f w + g w := rfl
  rw [hfgw]
  have hle : ‖f w + g w‖ ≤ ‖f w‖ + ‖g w‖ := norm_add_le _ _
  have h2 : ‖f w + g w‖ ^ 2 ≤ (‖f w‖ + ‖g w‖) ^ 2 := by gcongr
  nlinarith [h2, sq_nonneg (‖f w‖ - ‖g w‖)]

/-- Finite `L²` energy is preserved under scalar multiplication. -/
lemma integrableOn_normSq_smul (c : ℂ) {f : ℂ → ℂ}
    (hfi : IntegrableOn (fun w => ‖f w‖ ^ 2) disk) :
    IntegrableOn (fun w => ‖(c • f) w‖ ^ 2) disk := by
  have hrw : (fun w => ‖(c • f) w‖ ^ 2) = fun w => ‖c‖ ^ 2 * ‖f w‖ ^ 2 := by
    funext w; simp only [Pi.smul_apply, norm_smul, mul_pow]
  rw [hrw]; exact hfi.const_mul _

/-- Smooth copy fields with finite Dirichlet and squared-norm integrals and
both representative normalizations. This is a submodule of pointwise fields. -/
def EnergySmooth (k m : ℕ) : Submodule ℂ (ZMod (2 * m) → ℂ → ℂ) where
  carrier := {u | IsSmooth k m u ∧ (∀ n, IntegrableOn (gradSq (u n)) disk)
    ∧ (∀ n, IntegrableOn (fun w => ‖u n w‖ ^ 2) disk) ∧ PunctureZero k u ∧ SeamVal k u}
  zero_mem' := by
    refine ⟨isSmooth_zero k m, ?_, ?_, punctureZero_zero k m, seamVal_zero k m⟩
    · intro n
      have h0 : gradSq ((0 : ZMod (2 * m) → ℂ → ℂ) n) = fun _ => (0 : ℝ) := by
        funext w; simp [gradSq]
      rw [h0]; exact integrableOn_zero
    · intro n
      have h0 : (fun w => ‖(0 : ZMod (2 * m) → ℂ → ℂ) n w‖ ^ 2) = fun _ => (0 : ℝ) := by
        funext w; simp
      rw [h0]; exact integrableOn_zero
  add_mem' := fun {u v} hu hv =>
    ⟨isSmooth_add hu.1 hv.1,
     fun n => integrableOn_gradSq_add (fun w hw => differentiableAt_of_isSmooth hu.1 n hw)
       (fun w hw => differentiableAt_of_isSmooth hv.1 n hw) (hu.2.1 n) (hv.2.1 n),
     fun n => integrableOn_normSq_add (hu.1.1 n).continuousOn (hv.1.1 n).continuousOn
       (hu.2.2.1 n) (hv.2.2.1 n),
     punctureZero_add hu.2.2.2.1 hv.2.2.2.1,
     seamVal_add hu.2.2.2.2 hv.2.2.2.2⟩
  smul_mem' := fun c u hu =>
    ⟨isSmooth_smul c hu.1,
     fun n => integrableOn_gradSq_smul c (fun w hw => differentiableAt_of_isSmooth hu.1 n hw)
       (hu.2.1 n),
     fun n => integrableOn_normSq_smul c (hu.2.2.1 n),
     punctureZero_smul c hu.2.2.2.1,
     seamVal_smul c hu.2.2.2.2⟩

/-! ### Integrability estimates for `jacobiB` on smooth finite-energy fields -/

/-- Operator-norm bound by the two coordinate values: `‖A‖ ≤ ‖A 1‖ + ‖A I‖` for the real-linear
`A = fderiv ℝ f w`.  Lets finite Dirichlet energy control `‖fderiv‖` pointwise. -/
lemma fderiv_opNorm_le (f : ℂ → ℂ) (w : ℂ) :
    ‖fderiv ℝ f w‖ ≤ ‖fderiv ℝ f w 1‖ + ‖fderiv ℝ f w I‖ := by
  set A := fderiv ℝ f w with hA
  refine A.opNorm_le_bound (by positivity) fun z => ?_
  have hz : z = z.re • (1 : ℂ) + z.im • I := by
    apply Complex.ext <;> simp
  calc ‖A z‖ = ‖z.re • A 1 + z.im • A I‖ := by
        conv_lhs => rw [hz]
        rw [map_add, map_smul, map_smul]
    _ ≤ |z.re| * ‖A 1‖ + |z.im| * ‖A I‖ := by
        refine (norm_add_le _ _).trans_eq ?_
        rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs]
    _ ≤ ‖z‖ * ‖A 1‖ + ‖z‖ * ‖A I‖ := by
        gcongr
        · exact abs_re_le_norm z
        · exact abs_im_le_norm z
    _ = (‖A 1‖ + ‖A I‖) * ‖z‖ := by ring

/-- On the finite-measure disk, a nonnegative measurable `h` with `h² ≤ g` (integrable) is itself
integrable — the elementary `L² ⊆ L¹` step, via `h ≤ (1 + h²)/2`. -/
lemma integrableOn_of_sq_le {h g : ℂ → ℝ}
    (hmeas : AEStronglyMeasurable h (volume.restrict disk)) (hnn : ∀ w ∈ disk, 0 ≤ h w)
    (hg : IntegrableOn g disk) (hle : ∀ w ∈ disk, h w ^ 2 ≤ g w) : IntegrableOn h disk := by
  have hconst : IntegrableOn (fun _ : ℂ => (1 : ℝ)) disk :=
    integrableOn_const measure_ball_lt_top.ne
  have hbound : IntegrableOn (fun w => (1 / 2 : ℝ) * ((fun _ : ℂ => (1 : ℝ)) w + g w)) disk :=
    (hconst.add hg).const_mul _
  refine hbound.mono' hmeas ?_
  refine ae_restrict_of_forall_mem measurableSet_disk fun w hw => ?_
  rw [Real.norm_of_nonneg (hnn w hw)]
  nlinarith [hle w hw, sq_nonneg (h w - 1), hnn w hw]

/-- The gradient pairing is integrable: finite Dirichlet energy (first slot) against a `Regular`
test with bounded gradient, using finite-measure L²-to-L¹ control. -/
lemma integrableOn_gradInner_left {u φ : ZMod (2 * m) → ℂ → ℂ} (n : ZMod (2 * m))
    (hui : IntegrableOn (gradSq (u n)) disk) (hφ : Regular φ) :
    IntegrableOn (gradInner (u n) (φ n)) disk := by
  obtain ⟨M, hM⟩ := exists_bound_fderiv hφ n
  have h1 : IntegrableOn (fun w => ‖fderiv ℝ (u n) w 1‖) disk := by
    refine integrableOn_of_sq_le
      ((measurable_fderiv_apply_const ℝ (u n) 1).norm).aestronglyMeasurable
      (fun _ _ => norm_nonneg _) hui (fun w _ => ?_)
    unfold gradSq; nlinarith [sq_nonneg ‖fderiv ℝ (u n) w I‖]
  have hI : IntegrableOn (fun w => ‖fderiv ℝ (u n) w I‖) disk := by
    refine integrableOn_of_sq_le
      ((measurable_fderiv_apply_const ℝ (u n) I).norm).aestronglyMeasurable
      (fun _ _ => norm_nonneg _) hui (fun w _ => ?_)
    unfold gradSq; nlinarith [sq_nonneg ‖fderiv ℝ (u n) w 1‖]
  have hdom : IntegrableOn
      (fun w => 2 * M * (‖fderiv ℝ (u n) w 1‖ + ‖fderiv ℝ (u n) w I‖)) disk :=
    (h1.add hI).const_mul (2 * M)
  refine hdom.mono' (measurable_gradInner _ _).aestronglyMeasurable ?_
  refine ae_restrict_of_forall_mem measurableSet_disk fun w hw => ?_
  calc ‖gradInner (u n) (φ n) w‖
      ≤ 2 * ‖fderiv ℝ (u n) w‖ * ‖fderiv ℝ (φ n) w‖ := norm_gradInner_le _ _ _
    _ ≤ 2 * (‖fderiv ℝ (u n) w 1‖ + ‖fderiv ℝ (u n) w I‖) * M := by
        gcongr
        · exact fderiv_opNorm_le _ _
        · exact hM w hw
    _ = 2 * M * (‖fderiv ℝ (u n) w 1‖ + ‖fderiv ℝ (u n) w I‖) := by ring

/-- The potential pairing is integrable: finite `L²` (first slot) against a bounded `Regular`
test. -/
lemma integrableOn_potDens_left {u φ : ZMod (2 * m) → ℂ → ℂ} (n : ZMod (2 * m))
    (hul : IntegrableOn (fun w => ‖u n w‖ ^ 2) disk) (hu_cont : ContinuousOn (u n) disk)
    (hφ : Regular φ) :
    IntegrableOn (fun w => (potV k w : ℂ) * (starRingEnd ℂ) (u n w) * φ n w) disk := by
  obtain ⟨Mφ, hMφ⟩ := exists_bound_val hφ n
  have hunorm : IntegrableOn (fun w => ‖u n w‖) disk :=
    integrableOn_of_sq_le (hu_cont.norm.aestronglyMeasurable measurableSet_disk)
      (fun _ _ => norm_nonneg _) hul (fun _ _ => le_refl _)
  have hdom : IntegrableOn (fun w => 8 * ((k : ℝ) - 1) ^ 2 * Mφ * ‖u n w‖) disk :=
    hunorm.const_mul _
  have hpotV : ContinuousOn (fun w => (potV k w : ℂ)) disk :=
    (Complex.continuous_ofReal.comp (continuous_potV k)).continuousOn
  have hconj : ContinuousOn (fun w => (starRingEnd ℂ) (u n w)) disk :=
    Complex.continuous_conj.comp_continuousOn hu_cont
  have hcont : ContinuousOn (fun w => (potV k w : ℂ) * (starRingEnd ℂ) (u n w) * φ n w) disk :=
    (hpotV.mul hconj).mul (hφ.1 n).continuousOn
  refine hdom.mono' (hcont.aestronglyMeasurable measurableSet_disk) ?_
  refine ae_restrict_of_forall_mem measurableSet_disk fun w hw => ?_
  have hpv : ‖(potV k w : ℂ)‖ = potV k w := by
    rw [Complex.norm_real, Real.norm_of_nonneg (potV_nonneg k w)]
  calc ‖(potV k w : ℂ) * (starRingEnd ℂ) (u n w) * φ n w‖
      = potV k w * ‖u n w‖ * ‖φ n w‖ := by
        rw [norm_mul, norm_mul, Complex.norm_conj, hpv]
    _ ≤ 8 * ((k : ℝ) - 1) ^ 2 * ‖u n w‖ * Mφ := by
        gcongr
        · exact potV_le (le_of_lt (mem_disk_iff.mp hw))
        · exact hMφ w hw
    _ = 8 * ((k : ℝ) - 1) ^ 2 * Mφ * ‖u n w‖ := by ring

/-- `gradInner` is conjugate-linear in its first slot — derived from `gradInner_conj` +
`gradInner_smul_right`. -/
lemma gradInner_smul_left (c : ℂ) {f g : ℂ → ℂ} {w : ℂ} (hf : DifferentiableAt ℝ f w) :
    gradInner (c • f) g w = (starRingEnd ℂ) c * gradInner f g w := by
  have key : (starRingEnd ℂ) (gradInner (c • f) g w)
      = (starRingEnd ℂ) ((starRingEnd ℂ) c * gradInner f g w) := by
    rw [← gradInner_conj (c • f) g w, gradInner_smul_right c hf, map_mul, Complex.conj_conj,
      ← gradInner_conj f g w]
  simpa only [Complex.conj_conj] using congrArg (starRingEnd ℂ) key

/-! ### First-slot additivity and conjugate-linearity of `jacobiB` against `CcSmooth` tests -/

/-- `jacobiB` is additive in the first slot on `EnergySmooth`, tested against `CcSmooth`. -/
lemma jacobiB_add_left_mem [NeZero m] {u u' φ : ZMod (2 * m) → ℂ → ℂ}
    (hu : u ∈ EnergySmooth k m) (hu' : u' ∈ EnergySmooth k m) (hφ : φ ∈ CcSmooth k m) :
    jacobiB k m (u + u') φ = jacobiB k m u φ + jacobiB k m u' φ := by
  have h2m : NeZero (2 * m) := ⟨by have := NeZero.ne m; omega⟩
  have hφr : Regular φ := regular_of_mem hφ
  unfold jacobiB
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun n _ => ?_
  have hg1 : ∫ w in disk, gradInner ((u + u') n) (φ n) w
      = (∫ w in disk, gradInner (u n) (φ n) w) + ∫ w in disk, gradInner (u' n) (φ n) w := by
    rw [← integral_add (integrableOn_gradInner_left n (hu.2.1 n) hφr)
      (integrableOn_gradInner_left n (hu'.2.1 n) hφr)]
    refine setIntegral_congr_fun measurableSet_disk fun w hw => ?_
    exact gradInner_add_left (differentiableAt_of_isSmooth hu.1 n hw)
      (differentiableAt_of_isSmooth hu'.1 n hw)
  have hp1 : ∫ w in disk, (potV k w : ℂ) * (starRingEnd ℂ) ((u + u') n w) * φ n w
      = (∫ w in disk, (potV k w : ℂ) * (starRingEnd ℂ) (u n w) * φ n w)
        + ∫ w in disk, (potV k w : ℂ) * (starRingEnd ℂ) (u' n w) * φ n w := by
    rw [← integral_add (integrableOn_potDens_left n (hu.2.2.1 n) (hu.1.1 n).continuousOn hφr)
      (integrableOn_potDens_left n (hu'.2.2.1 n) (hu'.1.1 n).continuousOn hφr)]
    refine setIntegral_congr_fun measurableSet_disk fun w _ => ?_
    simp only [Pi.add_apply, map_add]
    ring
  rw [hg1, hp1]; ring

/-- `jacobiB` is conjugate-linear in the first slot on `EnergySmooth`, tested against `CcSmooth`. -/
lemma jacobiB_smul_left_mem [NeZero m] {u φ : ZMod (2 * m) → ℂ → ℂ} (c : ℂ)
    (hu : u ∈ EnergySmooth k m) (hφ : φ ∈ CcSmooth k m) :
    jacobiB k m (c • u) φ = (starRingEnd ℂ) c * jacobiB k m u φ := by
  have h2m : NeZero (2 * m) := ⟨by have := NeZero.ne m; omega⟩
  have hφr : Regular φ := regular_of_mem hφ
  unfold jacobiB
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun n _ => ?_
  have hg : ∫ w in disk, gradInner ((c • u) n) (φ n) w
      = (starRingEnd ℂ) c * ∫ w in disk, gradInner (u n) (φ n) w := by
    rw [← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_disk fun w hw => ?_
    exact gradInner_smul_left c (differentiableAt_of_isSmooth hu.1 n hw)
  have hp : ∫ w in disk, (potV k w : ℂ) * (starRingEnd ℂ) ((c • u) n w) * φ n w
      = (starRingEnd ℂ) c * ∫ w in disk, (potV k w : ℂ) * (starRingEnd ℂ) (u n w) * φ n w := by
    rw [← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_disk fun w _ => ?_
    simp only [Pi.smul_apply, smul_eq_mul, map_mul]
    ring
  rw [hg, hp]; ring

/-- `jacobiB` vanishes when the first slot is `0`. -/
lemma jacobiB_zero_left [NeZero m] (φ : ZMod (2 * m) → ℂ → ℂ) :
    jacobiB k m (0 : ZMod (2 * m) → ℂ → ℂ) φ = 0 := by
  have h2m : NeZero (2 * m) := ⟨by have := NeZero.ne m; omega⟩
  unfold jacobiB
  refine Finset.sum_eq_zero fun n _ => ?_
  have hg : (∫ w in disk, gradInner ((0 : ZMod (2 * m) → ℂ → ℂ) n) (φ n) w) = 0 := by
    have h0 : ∀ w, gradInner ((0 : ZMod (2 * m) → ℂ → ℂ) n) (φ n) w = 0 := fun w => by
      simp [gradInner]
    simp only [h0, integral_zero]
  have hp : (∫ w in disk, (potV k w : ℂ) * (starRingEnd ℂ) ((0 : ZMod (2 * m) → ℂ → ℂ) n w)
      * φ n w) = 0 := by
    have h0 : ∀ w, (potV k w : ℂ) * (starRingEnd ℂ) ((0 : ZMod (2 * m) → ℂ → ℂ) n w) * φ n w = 0 :=
      fun w => by simp
    simp only [h0, integral_zero]
  rw [hg, hp, sub_zero]

/-- The Jacobi kernel on `EnergySmooth`, defined by vanishing against every
`CcSmooth` test. Identification with a radical tested on a larger domain is
a separate comparison, not part of this definition. -/
def WeakKer (k m : ℕ) [NeZero m] : Submodule ℂ (ZMod (2 * m) → ℂ → ℂ) where
  carrier := {u | u ∈ EnergySmooth k m ∧ ∀ φ, φ ∈ CcSmooth k m → jacobiB k m u φ = 0}
  zero_mem' := ⟨(EnergySmooth k m).zero_mem, fun φ _ => jacobiB_zero_left φ⟩
  add_mem' := fun {u v} hu hv =>
    ⟨(EnergySmooth k m).add_mem hu.1 hv.1, fun φ hφ => by
      rw [jacobiB_add_left_mem hu.1 hv.1 hφ, hu.2 φ hφ, hv.2 φ hφ, add_zero]⟩
  smul_mem' := fun c u hu =>
    ⟨(EnergySmooth k m).smul_mem c hu.1, fun φ hφ => by
      rw [jacobiB_smul_left_mem c hu.1 hφ, hu.2 φ hφ, mul_zero]⟩

end KsIndex.FaithfulInjection
