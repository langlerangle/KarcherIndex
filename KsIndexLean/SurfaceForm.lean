module

/-
# Polarized Jacobi form on the disk-chain coordinate domain

The coordinate index `Surface.indSurface` uses the real quadratic form `jacobiQ`.
To decompose it over symmetry sectors, this file supplies its complex polarized
form `jacobiB` and proves sesquilinearity on `Surface.CcSmooth`.

For `k ≥ 2` and `m ≠ 0`, `jacobiB_self` identifies the diagonal with the complex
coercion of `jacobiQ`. This identity uses conformal collapse and does not require
an integrability assumption. Additivity of the polarized form does require
integrability of the cross densities, established here on regular families.

`exists_smooth_rep` proves that each disk restriction of a member of `CcSmooth`
agrees, on the open disk near any point of its closure, with a function smooth
at that point. The four cases are interior, puncture, direct seam and reflected
seam. Agreement is asserted on the open disk; it does not identify every stored
receiving-seam value of the total-function representative.

Compactness then bounds the values and derivatives on the disk, giving
integrability of the gradient and potential cross densities. The predicate
`Regular` records the local extension property, allowing `sesq_of_regular` to
apply to any subspace satisfying it. Finally, `sesq_surface` gives the structure
on the uncurried domain `Dom k m` used by `indSurface`.
-/
public import KsIndexLean.GradOrtho
public import KsIndexLean.FormIndexSum

@[expose] public section


noncomputable section

open Complex Real MeasureTheory Filter Topology
open scoped ContDiff

namespace KsIndex.SurfaceForm

open KsIndex.Surface KsIndex.GradOrtho KsIndex.Radial KsIndex.FormIndex

/-! ### Pointwise algebra of the gradient cross density -/

lemma gradInner_add_left {f g h : ℂ → ℂ} {w : ℂ} (hf : DifferentiableAt ℝ f w)
    (hg : DifferentiableAt ℝ g w) :
    gradInner (f + g) h w = gradInner f h w + gradInner g h w := by
  simp only [gradInner, fderiv_add hf hg, FunLike.coe_add, Pi.add_apply, map_add]
  ring

lemma gradInner_add_right {f g h : ℂ → ℂ} {w : ℂ} (hg : DifferentiableAt ℝ g w)
    (hh : DifferentiableAt ℝ h w) :
    gradInner f (g + h) w = gradInner f g w + gradInner f h w := by
  simp only [gradInner, fderiv_add hg hh, FunLike.coe_add, Pi.add_apply]
  ring

lemma gradInner_smul_right {f g : ℂ → ℂ} {w : ℂ} (c : ℂ) (hg : DifferentiableAt ℝ g w) :
    gradInner f (c • g) w = c * gradInner f g w := by
  simp only [gradInner, fderiv_const_smul hg, FunLike.coe_smul, Pi.smul_apply,
    smul_eq_mul]
  ring

lemma gradInner_conj (f g : ℂ → ℂ) (w : ℂ) :
    gradInner g f w = (starRingEnd ℂ) (gradInner f g w) := by
  simp only [gradInner, map_add, map_mul, Complex.conj_conj]
  ring

lemma norm_gradInner_le (f g : ℂ → ℂ) (w : ℂ) :
    ‖gradInner f g w‖ ≤ 2 * ‖fderiv ℝ f w‖ * ‖fderiv ℝ g w‖ := by
  set L := fderiv ℝ f w
  set M := fderiv ℝ g w
  have hL1 : ‖L 1‖ ≤ ‖L‖ := by simpa using L.le_opNorm 1
  have hLI : ‖L I‖ ≤ ‖L‖ := by simpa [Complex.norm_I] using L.le_opNorm I
  have hM1 : ‖M 1‖ ≤ ‖M‖ := by simpa using M.le_opNorm 1
  have hMI : ‖M I‖ ≤ ‖M‖ := by simpa [Complex.norm_I] using M.le_opNorm I
  calc ‖gradInner f g w‖
      ≤ ‖(starRingEnd ℂ) (L 1) * M 1‖ + ‖(starRingEnd ℂ) (L I) * M I‖ := norm_add_le _ _
    _ = ‖L 1‖ * ‖M 1‖ + ‖L I‖ * ‖M I‖ := by simp only [norm_mul, Complex.norm_conj]
    _ ≤ ‖L‖ * ‖M‖ + ‖L‖ * ‖M‖ :=
        add_le_add (mul_le_mul hL1 hM1 (norm_nonneg _) (norm_nonneg _))
          (mul_le_mul hLI hMI (norm_nonneg _) (norm_nonneg _))
    _ = 2 * ‖L‖ * ‖M‖ := by ring

/-! ### The polarized Jacobi form -/

/-- The polarized Jacobi form on `Ξ_{k,m}`, through the flat densities on each half period:
`jacobiB u v = ∑_n (∫_D ⟨∇u_n, ∇v_n⟩ − ∫_D V_k · ū_n · v_n)`. -/
def jacobiB (k m : ℕ) [NeZero m] (u v : ZMod (2 * m) → ℂ → ℂ) : ℂ :=
  have : NeZero (2 * m) := ⟨by have := NeZero.ne m; omega⟩
  ∑ n : ZMod (2 * m),
    ((∫ w in disk, gradInner (u n) (v n) w)
      - ∫ w in disk, (potV k w : ℂ) * (starRingEnd ℂ) (u n w) * v n w)

/-- The diagonal of the polarized form is the Jacobi quadratic form. -/
lemma jacobiB_self {k m : ℕ} [NeZero m] (hk : 2 ≤ k) (u : ZMod (2 * m) → ℂ → ℂ) :
    jacobiB k m u u = (jacobiQ k m u : ℂ) := by
  have : NeZero (2 * m) := ⟨by have := NeZero.ne m; omega⟩
  unfold jacobiB jacobiQ
  rw [Complex.ofReal_sum]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [dirichletG_sub_potentialG hk, Complex.ofReal_sub]
  have e1 : ∫ w in disk, ((gradSq (u n) w : ℝ) : ℂ) = ((∫ w in disk, gradSq (u n) w : ℝ) : ℂ) :=
    integral_ofReal
  have e2 : ∫ w in disk, ((potV k w * ‖u n w‖ ^ 2 : ℝ) : ℂ)
      = ((∫ w in disk, potV k w * ‖u n w‖ ^ 2 : ℝ) : ℂ) := integral_ofReal
  rw [← e1, ← e2]
  congr 1
  · exact integral_congr_ae (Eventually.of_forall fun w => gradInner_self (u n) w)
  · refine integral_congr_ae (Eventually.of_forall fun w => ?_)
    push_cast
    rw [mul_assoc, Complex.conj_mul']

/-! ### Regularity up to the boundary -/

lemma measurableSet_disk : MeasurableSet disk := by rw [disk]; exact measurableSet_ball

lemma mem_disk_iff {w : ℂ} : w ∈ disk ↔ ‖w‖ < 1 := by
  rw [disk, Metric.mem_ball, dist_zero_right]

/-- Points of the unit circle off the punctures lie on one of the two arc families. -/
lemma mem_arc_of_not_puncture {k : ℕ} {w : ℂ} (hw : ‖w‖ = 1) (hp : w ∉ punctures k) :
    w ∈ arc k 0 ∨ w ∈ arc k 1 := by
  have hre : (w ^ k).re ≠ 0 := by
    intro h0
    apply hp
    change w ^ (2 * k) = -1
    have hnorm : ‖w ^ k‖ = 1 := by rw [norm_pow, hw, one_pow]
    have him : (w ^ k).im ^ 2 = 1 := by
      have := KsIndex.JacobiMode.nsq (w ^ k)
      rw [hnorm, h0] at this
      linarith
    rw [pow_mul']
    apply Complex.ext
    · simp only [sq, Complex.mul_re, h0, Complex.neg_re, Complex.one_re]
      nlinarith [him]
    · simp [sq, Complex.mul_im, h0]
  rcases lt_or_gt_of_ne hre with h | h
  · left; exact ⟨hw, by simpa using h⟩
  · right; exact ⟨hw, by simpa using h⟩

lemma seamArc_pred (k m : ℕ) (n : ZMod (2 * m)) :
    seamArc k m (n - 1) = arc k (parity m n).val := by
  simp [seamArc]

lemma parity_succ_val (m : ℕ) (n : ZMod (2 * m)) :
    (parity m (n + 1)).val = 1 - (parity m n).val := by
  rw [map_add, map_one]
  generalize parity m n = x
  revert x
  decide

/-- **Local smooth representative.**  At every point `w₀` of the closed disk, a `C_c^∞` function
agrees on the disk near `w₀` with a function that is `C^∞` at `w₀`. -/
lemma exists_smooth_rep {k m : ℕ} {u : ZMod (2 * m) → ℂ → ℂ} (hu : u ∈ CcSmooth k m)
    (n : ZMod (2 * m)) {w₀ : ℂ} (hw₀ : ‖w₀‖ ≤ 1) :
    ∃ F : ℂ → ℂ, ContDiffAt ℝ ∞ F w₀ ∧ ∀ᶠ w in 𝓝 w₀, w ∈ disk → u n w = F w := by
  obtain ⟨hsm, hsupp⟩ := hu
  rcases lt_or_eq_of_le hw₀ with hlt | heq
  · -- interior point
    have hw : w₀ ∈ disk := mem_disk_iff.mpr hlt
    exact ⟨u n, (hsm.1 n).contDiffAt (Metric.isOpen_ball.mem_nhds hw),
      Eventually.of_forall fun _ _ => rfl⟩
  · by_cases hp : w₀ ∈ punctures k
    · -- puncture: `u` vanishes nearby
      obtain ⟨ε, hε, hz⟩ := hsupp
      refine ⟨0, contDiffAt_const, ?_⟩
      filter_upwards [Metric.ball_mem_nhds w₀ hε] with w hw _
      exact hz n w ⟨w₀, hp, by rwa [Metric.mem_ball, dist_eq_norm] at hw⟩
    · -- seam point: on one of the two arc families
      have harc := mem_arc_of_not_puncture heq hp
      have hpv := parity_succ_val m n
      have hlt2 := ZMod.val_lt (parity m n)
      have hcases : w₀ ∈ seamArc k m n ∨ w₀ ∈ seamArc k m (n - 1) := by
        rw [seamArc_pred]
        unfold seamArc
        rw [hpv]
        rcases (by omega : (parity m n).val = 0 ∨ (parity m n).val = 1) with h | h <;>
          rcases harc with h0 | h1 <;> rw [h]
        · exact Or.inr h0
        · exact Or.inl h1
        · exact Or.inl h0
        · exact Or.inr h1
      rcases hcases with hA | hB
      · -- direct seam: `glue u n` is the representative
        refine ⟨glue u n, hsm.2.1 n w₀ hA, Eventually.of_forall fun w hw => ?_⟩
        have : ‖w‖ ≤ 1 := le_of_lt (mem_disk_iff.mp hw)
        simp [glue, this]
      · -- reflected seam: `glue u (n-1) ∘ (w ↦ 1/w̄)` is the representative
        set σ : ℂ → ℂ := fun w => 1 / (starRingEnd ℂ) w with hσ
        have hw0 : w₀ ≠ 0 := by rintro rfl; simp at heq
        have hσw₀ : σ w₀ = w₀ := by
          simp only [hσ, one_div]
          exact inv_eq_of_mul_eq_one_right (by rw [Complex.conj_mul', heq]; norm_num)
        have hσC : ContDiffAt ℝ ∞ σ w₀ := by
          have h1 : ContDiffAt ℝ ∞ (fun w : ℂ => (starRingEnd ℂ) w) w₀ := by
            have := (Complex.conjCLE.contDiff (n := ∞)).contDiffAt (x := w₀)
            exact this.congr_of_eventuallyEq (Eventually.of_forall fun w => by
              simp [Complex.conjCAE_apply])
          have h2 : ContDiffAt ℝ ∞ (Inv.inv : ℂ → ℂ) ((starRingEnd ℂ) w₀) :=
            contDiffAt_inv ℝ (by simpa using hw0)
          simp only [hσ, one_div]
          exact h2.comp w₀ h1
        refine ⟨glue u (n - 1) ∘ σ, ?_, ?_⟩
        · have hg : ContDiffAt ℝ ∞ (glue u (n - 1)) (σ w₀) := by
            rw [hσw₀]; exact hsm.2.1 (n - 1) w₀ hB
          exact hg.comp w₀ hσC
        · filter_upwards [eventually_ne_nhds hw0] with w hwne hw
          have hlt' : ‖w‖ < 1 := mem_disk_iff.mp hw
          have hgt : ¬ ‖σ w‖ ≤ 1 := by
            simp only [hσ, one_div, norm_inv, Complex.norm_conj, not_le]
            exact (one_lt_inv₀ (norm_pos_iff.mpr hwne)).mpr hlt'
          simp only [Function.comp, glue, hgt, if_false, sub_add_cancel]
          congr 1
          simp only [hσ, one_div, map_inv₀, Complex.conj_conj, inv_inv]

/-- **Regular families**: smooth on each open disk and, at every point of the closed disk, agreeing
on the disk near that point with a function `C^∞` there.  `C_c^∞(Ξ_{k,m})` is regular
(`regular_of_mem`); so are the larger Neumann-type test spaces of the one-period problem, which is
why the integrability and sesquilinearity lemmas below are stated for regular families. -/
def Regular {m : ℕ} (u : ZMod (2 * m) → ℂ → ℂ) : Prop :=
  (∀ n, ContDiffOn ℝ ∞ (u n) disk)
    ∧ ∀ n (w₀ : ℂ), ‖w₀‖ ≤ 1 → ∃ F : ℂ → ℂ, ContDiffAt ℝ ∞ F w₀ ∧
        ∀ᶠ w in 𝓝 w₀, w ∈ disk → u n w = F w

lemma regular_of_mem {k m : ℕ} {u : ZMod (2 * m) → ℂ → ℂ} (hu : u ∈ CcSmooth k m) : Regular u :=
  ⟨hu.1.1, fun n _ hw₀ => exists_smooth_rep hu n hw₀⟩

/-- **Compactness**: a function locally bounded (on the disk) near every point of the closed disk
is bounded on the disk. -/
lemma bounded_on_disk_of_local {E : Type*} [NormedAddCommGroup E] {φ : ℂ → E}
    (h : ∀ w₀ : ℂ, ‖w₀‖ ≤ 1 → ∃ M : ℝ, ∀ᶠ w in 𝓝 w₀, w ∈ disk → ‖φ w‖ ≤ M) :
    ∃ M : ℝ, ∀ w ∈ disk, ‖φ w‖ ≤ M := by
  choose! M hM using h
  have hK : IsCompact (Metric.closedBall (0 : ℂ) 1) := ProperSpace.isCompact_closedBall 0 1
  obtain ⟨t, -, ht⟩ := hK.elim_nhds_subcover (fun w₀ => {w | w ∈ disk → ‖φ w‖ ≤ M w₀})
    (fun w₀ hw₀ => hM w₀ (by simpa using hw₀))
  refine ⟨∑ x ∈ t, |M x|, fun w hw => ?_⟩
  have hwK : w ∈ Metric.closedBall (0 : ℂ) 1 := Metric.ball_subset_closedBall hw
  obtain ⟨x, hxt, hx⟩ := Set.mem_iUnion₂.mp (ht hwK)
  calc ‖φ w‖ ≤ M x := hx hw
    _ ≤ |M x| := le_abs_self _
    _ ≤ ∑ x ∈ t, |M x| :=
        Finset.single_le_sum (f := fun x => |M x|) (fun _ _ => abs_nonneg _) hxt

lemma local_bound_val {m : ℕ} {u : ZMod (2 * m) → ℂ → ℂ} (hu : Regular u)
    (n : ZMod (2 * m)) {w₀ : ℂ} (hw₀ : ‖w₀‖ ≤ 1) :
    ∃ M : ℝ, ∀ᶠ w in 𝓝 w₀, w ∈ disk → ‖u n w‖ ≤ M := by
  obtain ⟨F, hF, hFeq⟩ := hu.2 n w₀ hw₀
  refine ⟨‖F w₀‖ + 1, ?_⟩
  have hc : ∀ᶠ w in 𝓝 w₀, ‖F w‖ < ‖F w₀‖ + 1 :=
    hF.continuousAt.norm.eventually_lt continuousAt_const (by linarith)
  filter_upwards [hc, hFeq] with w hw1 hw2 hwd
  rw [hw2 hwd]
  exact le_of_lt hw1

lemma local_bound_fderiv {m : ℕ} {u : ZMod (2 * m) → ℂ → ℂ} (hu : Regular u)
    (n : ZMod (2 * m)) {w₀ : ℂ} (hw₀ : ‖w₀‖ ≤ 1) :
    ∃ M : ℝ, ∀ᶠ w in 𝓝 w₀, w ∈ disk → ‖fderiv ℝ (u n) w‖ ≤ M := by
  obtain ⟨F, hF, hFeq⟩ := hu.2 n w₀ hw₀
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.mp hFeq
  have hcont : ContinuousAt (fderiv ℝ F) w₀ := hF.continuousAt_fderiv (by simp)
  have hc : ∀ᶠ w in 𝓝 w₀, ‖fderiv ℝ F w‖ < ‖fderiv ℝ F w₀‖ + 1 :=
    hcont.norm.eventually_lt continuousAt_const (by linarith)
  refine ⟨‖fderiv ℝ F w₀‖ + 1, ?_⟩
  filter_upwards [hc, Metric.ball_mem_nhds w₀ hε] with w hw1 hw2 hwd
  have hopen : IsOpen (Metric.ball w₀ ε ∩ disk) := Metric.isOpen_ball.inter Metric.isOpen_ball
  have hmem : Metric.ball w₀ ε ∩ disk ∈ 𝓝 w := hopen.mem_nhds ⟨hw2, hwd⟩
  have heq : u n =ᶠ[𝓝 w] F :=
    eventually_of_mem hmem fun w' hw' => hball (Metric.mem_ball.mp hw'.1) hw'.2
  rw [heq.fderiv_eq]
  exact le_of_lt hw1

lemma exists_bound_val {m : ℕ} {u : ZMod (2 * m) → ℂ → ℂ} (hu : Regular u)
    (n : ZMod (2 * m)) : ∃ M : ℝ, ∀ w ∈ disk, ‖u n w‖ ≤ M :=
  bounded_on_disk_of_local fun _ hw₀ => local_bound_val hu n hw₀

lemma exists_bound_fderiv {m : ℕ} {u : ZMod (2 * m) → ℂ → ℂ} (hu : Regular u)
    (n : ZMod (2 * m)) : ∃ M : ℝ, ∀ w ∈ disk, ‖fderiv ℝ (u n) w‖ ≤ M :=
  bounded_on_disk_of_local fun _ hw₀ => local_bound_fderiv hu n hw₀

/-! ### Integrability of the densities -/

lemma differentiableAt_of_regular {m : ℕ} {u : ZMod (2 * m) → ℂ → ℂ} (hu : Regular u)
    (n : ZMod (2 * m)) {w : ℂ} (hw : w ∈ disk) : DifferentiableAt ℝ (u n) w :=
  ((hu.1 n).contDiffAt (Metric.isOpen_ball.mem_nhds hw)).differentiableAt (by simp)

lemma differentiableAt_of_mem {k m : ℕ} {u : ZMod (2 * m) → ℂ → ℂ} (hu : u ∈ CcSmooth k m)
    (n : ZMod (2 * m)) {w : ℂ} (hw : w ∈ disk) : DifferentiableAt ℝ (u n) w :=
  differentiableAt_of_regular (regular_of_mem hu) n hw

lemma measurable_gradInner (f g : ℂ → ℂ) : Measurable (gradInner f g) := by
  unfold gradInner
  have m1 : Measurable fun w => fderiv ℝ f w 1 := measurable_fderiv_apply_const ℝ f 1
  have mI : Measurable fun w => fderiv ℝ f w I := measurable_fderiv_apply_const ℝ f I
  have n1 : Measurable fun w => fderiv ℝ g w 1 := measurable_fderiv_apply_const ℝ g 1
  have nI : Measurable fun w => fderiv ℝ g w I := measurable_fderiv_apply_const ℝ g I
  exact ((Complex.continuous_conj.measurable.comp m1).mul n1).add
    ((Complex.continuous_conj.measurable.comp mI).mul nI)

lemma integrableOn_gradInner {m : ℕ} {u v : ZMod (2 * m) → ℂ → ℂ} (hu : Regular u)
    (hv : Regular v) (n : ZMod (2 * m)) :
    IntegrableOn (gradInner (u n) (v n)) disk := by
  obtain ⟨Mu, hMu⟩ := exists_bound_fderiv hu n
  obtain ⟨Mv, hMv⟩ := exists_bound_fderiv hv n
  have h0 : (0 : ℂ) ∈ disk := mem_disk_iff.mpr (by simp)
  have hMu0 : 0 ≤ Mu := le_trans (norm_nonneg _) (hMu 0 h0)
  have hMv0 : 0 ≤ Mv := le_trans (norm_nonneg _) (hMv 0 h0)
  refine IntegrableOn.of_bound measure_ball_lt_top
    (measurable_gradInner _ _).aestronglyMeasurable.restrict (2 * Mu * Mv) ?_
  refine ae_restrict_of_forall_mem measurableSet_disk fun w hw => ?_
  calc ‖gradInner (u n) (v n) w‖
      ≤ 2 * ‖fderiv ℝ (u n) w‖ * ‖fderiv ℝ (v n) w‖ := norm_gradInner_le _ _ _
    _ ≤ 2 * Mu * Mv := by
        have := hMu w hw; have := hMv w hw
        gcongr

lemma continuous_potV (k : ℕ) : Continuous (potV k) := by
  have heq : potV k = fun w : ℂ => Vrad k ‖w‖ := funext fun w => potV_eq_Vrad k w
  rw [heq]
  exact (continuous_Vrad k).comp continuous_norm

lemma potV_nonneg (k : ℕ) (w : ℂ) : 0 ≤ potV k w := by
  unfold potV; positivity

lemma potV_le {k : ℕ} {w : ℂ} (hw : ‖w‖ ≤ 1) : potV k w ≤ 8 * ((k : ℝ) - 1) ^ 2 := by
  unfold potV
  have h0 : 0 ≤ ‖w‖ := norm_nonneg w
  have hp : ‖w‖ ^ (2 * k - 4) ≤ 1 := pow_le_one₀ h0 hw
  have hd : 1 ≤ (‖w‖ ^ (2 * k - 2) + 1) ^ 2 := by
    have : 0 ≤ ‖w‖ ^ (2 * k - 2) := by positivity
    nlinarith
  rw [div_le_iff₀ (by positivity)]
  have hc : 0 ≤ 8 * ((k : ℝ) - 1) ^ 2 := by positivity
  nlinarith [mul_le_mul_of_nonneg_left hp hc, mul_le_mul_of_nonneg_left hd hc]

lemma integrableOn_potDens {k m : ℕ} {u v : ZMod (2 * m) → ℂ → ℂ} (hu : Regular u)
    (hv : Regular v) (n : ZMod (2 * m)) :
    IntegrableOn (fun w => (potV k w : ℂ) * (starRingEnd ℂ) (u n w) * v n w) disk := by
  obtain ⟨Mu, hMu⟩ := exists_bound_val hu n
  obtain ⟨Mv, hMv⟩ := exists_bound_val hv n
  set C : ℝ := 8 * ((k : ℝ) - 1) ^ 2 with hCdef
  have h0 : (0 : ℂ) ∈ disk := mem_disk_iff.mpr (by simp)
  have hMu0 : 0 ≤ Mu := le_trans (norm_nonneg _) (hMu 0 h0)
  have hMv0 : 0 ≤ Mv := le_trans (norm_nonneg _) (hMv 0 h0)
  have hC0 : 0 ≤ C := by positivity
  have hcont : ContinuousOn (fun w => (potV k w : ℂ) * (starRingEnd ℂ) (u n w) * v n w) disk :=
    ((Complex.continuous_ofReal.comp (continuous_potV k)).continuousOn.mul
      (Complex.continuous_conj.comp_continuousOn (hu.1 n).continuousOn)).mul
      (hv.1 n).continuousOn
  refine IntegrableOn.of_bound measure_ball_lt_top
    (hcont.aestronglyMeasurable measurableSet_disk) (C * Mu * Mv) ?_
  refine ae_restrict_of_forall_mem measurableSet_disk fun w hw => ?_
  have hCw : ‖(potV k w : ℂ)‖ ≤ C := by
    rw [Complex.norm_real, Real.norm_of_nonneg (potV_nonneg k w)]
    exact potV_le (le_of_lt (mem_disk_iff.mp hw))
  calc ‖(potV k w : ℂ) * (starRingEnd ℂ) (u n w) * v n w‖
      = ‖(potV k w : ℂ)‖ * ‖u n w‖ * ‖v n w‖ := by
        simp only [norm_mul, Complex.norm_conj]
    _ ≤ C * Mu * Mv := by
        have := hMu w hw; have := hMv w hw
        gcongr

/-! ### Additivity of the polarized form on `C_c^∞` -/

lemma jacobiB_add_left {k m : ℕ} [NeZero m] {u u' v : ZMod (2 * m) → ℂ → ℂ}
    (hu : Regular u) (hu' : Regular u') (hv : Regular v) :
    jacobiB k m (u + u') v = jacobiB k m u v + jacobiB k m u' v := by
  have : NeZero (2 * m) := ⟨by have := NeZero.ne m; omega⟩
  unfold jacobiB
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun n _ => ?_
  have h1 : ∫ w in disk, gradInner ((u + u') n) (v n) w
      = (∫ w in disk, gradInner (u n) (v n) w) + ∫ w in disk, gradInner (u' n) (v n) w := by
    rw [← integral_add (integrableOn_gradInner hu hv n) (integrableOn_gradInner hu' hv n)]
    refine setIntegral_congr_fun measurableSet_disk fun w hw => ?_
    exact gradInner_add_left (differentiableAt_of_regular hu n hw)
      (differentiableAt_of_regular hu' n hw)
  have h2 : ∫ w in disk, (potV k w : ℂ) * (starRingEnd ℂ) ((u + u') n w) * v n w
      = (∫ w in disk, (potV k w : ℂ) * (starRingEnd ℂ) (u n w) * v n w)
        + ∫ w in disk, (potV k w : ℂ) * (starRingEnd ℂ) (u' n w) * v n w := by
    rw [← integral_add (integrableOn_potDens hu hv n) (integrableOn_potDens hu' hv n)]
    refine setIntegral_congr_fun measurableSet_disk fun w _ => ?_
    simp only [Pi.add_apply, map_add]
    ring
  rw [h1, h2]
  ring

lemma jacobiB_conj {k m : ℕ} [NeZero m] (u v : ZMod (2 * m) → ℂ → ℂ) :
    jacobiB k m v u = (starRingEnd ℂ) (jacobiB k m u v) := by
  have : NeZero (2 * m) := ⟨by have := NeZero.ne m; omega⟩
  unfold jacobiB
  rw [map_sum]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [map_sub, ← integral_conj, ← integral_conj]
  congr 1
  · exact integral_congr_ae (Eventually.of_forall fun w => gradInner_conj (u n) (v n) w)
  · refine integral_congr_ae (Eventually.of_forall fun w => ?_)
    simp only [map_mul, Complex.conj_ofReal, Complex.conj_conj]
    ring

lemma jacobiB_add_right {k m : ℕ} [NeZero m] {u v v' : ZMod (2 * m) → ℂ → ℂ}
    (hu : Regular u) (hv : Regular v) (hv' : Regular v') :
    jacobiB k m u (v + v') = jacobiB k m u v + jacobiB k m u v' := by
  rw [jacobiB_conj, jacobiB_add_left hv hv' hu, map_add, ← jacobiB_conj, ← jacobiB_conj]

lemma jacobiB_smul_right {k m : ℕ} [NeZero m] {u v : ZMod (2 * m) → ℂ → ℂ} (c : ℂ)
    (hv : Regular v) :
    jacobiB k m u (c • v) = c * jacobiB k m u v := by
  have : NeZero (2 * m) := ⟨by have := NeZero.ne m; omega⟩
  unfold jacobiB
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun n _ => ?_
  have h1 : ∫ w in disk, gradInner (u n) ((c • v) n) w
      = c * ∫ w in disk, gradInner (u n) (v n) w := by
    rw [← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_disk fun w hw => ?_
    exact gradInner_smul_right c (differentiableAt_of_regular hv n hw)
  have h2 : ∫ w in disk, (potV k w : ℂ) * (starRingEnd ℂ) (u n w) * (c • v) n w
      = c * ∫ w in disk, (potV k w : ℂ) * (starRingEnd ℂ) (u n w) * v n w := by
    rw [← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_disk fun w _ => ?_
    simp only [Pi.smul_apply, smul_eq_mul]
    ring
  rw [h1, h2]
  ring

/-! ### The sesquilinear structure in the uncurried coordinates of `indSurface` -/

/-- The test-function domain of `indSurface`, uncurried. -/
def Dom (k m : ℕ) : Submodule ℂ (ZMod (2 * m) × ℂ → ℂ) :=
  (CcSmooth k m).map (uncurryE m).toLinearMap

/-- The Jacobi quadratic form in uncurried coordinates (the form `indSurface` is built from). -/
def Qs (k m : ℕ) [NeZero m] (U : ZMod (2 * m) × ℂ → ℂ) : ℝ :=
  jacobiQ k m ((uncurryE m).symm U)

/-- The polarized Jacobi form in uncurried coordinates. -/
def Bs (k m : ℕ) [NeZero m] (U V : ZMod (2 * m) × ℂ → ℂ) : ℂ :=
  jacobiB k m ((uncurryE m).symm U) ((uncurryE m).symm V)

lemma indSurface_eq (k m : ℕ) [NeZero m] :
    indSurface k m = formIndex (Qs k m) (Dom k m) := rfl

lemma mem_Dom {k m : ℕ} {U : ZMod (2 * m) × ℂ → ℂ} :
    U ∈ Dom k m ↔ (uncurryE m).symm U ∈ CcSmooth k m :=
  Submodule.mem_map_equiv (CcSmooth k m)

/-- **The sesquilinear structure of the Jacobi form on any domain of regular families.** -/
theorem sesq_of_regular {k m : ℕ} [NeZero m] (hk : 2 ≤ k) (D : Submodule ℂ (ZMod (2 * m) × ℂ → ℂ))
    (hD : ∀ U ∈ D, Regular ((uncurryE m).symm U)) : Sesq (Qs k m) (Bs k m) D where
  self := fun U => jacobiB_self hk _
  addL := fun ha hb hv => by
    simp only [Bs, map_add]
    exact jacobiB_add_left (hD _ ha) (hD _ hb) (hD _ hv)
  addR := fun ha hv hw => by
    simp only [Bs, map_add]
    exact jacobiB_add_right (hD _ ha) (hD _ hv) (hD _ hw)
  conj := fun U V => jacobiB_conj _ _
  smulR := fun c _ hv => by
    simp only [Bs, map_smul]
    exact jacobiB_smul_right c (hD _ hv)

/-- **The sesquilinear structure of the Jacobi form on `C_c^∞(Ξ_{k,m})`.** -/
theorem sesq_surface {k m : ℕ} [NeZero m] (hk : 2 ≤ k) :
    Sesq (Qs k m) (Bs k m) (Dom k m) :=
  sesq_of_regular hk _ fun _ hU => regular_of_mem (mem_Dom.mp hU)

end KsIndex.SurfaceForm
