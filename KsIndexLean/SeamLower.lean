module

/-
# Negative finite families and puncture-cutoff stability

This file provides the linear-algebra and cutoff estimates used to obtain
seam index lower bounds. `formIndex_ge_of_neg` shows that a family of `n`
domain vectors whose every nonzero coefficient combination has negative
energy yields an index of at least `n`, assuming `Q 0 = 0`.

`DiskNice` records differentiability on the disk and uniform bounds for
the function and its Fréchet derivative. These bounds give the
integrability needed for the finite sesquilinear expansion `Bd_finsum`,
with conjugation in the first coefficient slot, for `k ≥ 2`.

For a finite set of positive frequencies with negative DtN symbols,
`eventually_eps_neg` proves that all sufficiently small positive puncture
cutoff scales preserve strict negativity of every combination with a
nonzero coefficient on that set. The proof combines the diagonal mode
energy, uniform bounds on finite combinations and the cutoff error
estimate. A fixed auxiliary parameter first makes the limiting error
smaller than the negative energy margin; the cutoff scale is then sent
to zero. `exists_eps_neg` gives the corresponding existential statement.

Placement of the cutoff modes in particular natural seam domains and
the resulting mode counts are assembled in subsequent files.
-/
public import KsIndexLean.CutoffContinuity

@[expose] public section


noncomputable section

open Complex MeasureTheory Filter
open scoped ContDiff

open KsIndex.PunctureCutoff KsIndex.JacobiMode
open Filter Topology

namespace KsIndex.FormIndex

open KsIndex.Surface KsIndex.GradOrtho KsIndex.SurfaceForm KsIndex.ModeDiag
  KsIndex.CutoffContinuity KsIndex.SingleDiskBridge

variable {ι : Type*}

/-- **Generic index lower bound.**  A finite-dimensional `Q`-negative subspace `V ≤ D` has
`finrank V ≤ formIndex Q D`. -/
theorem finrank_le_formIndex {Q : (ι → ℂ) → ℝ} {D : Submodule ℂ (ι → ℂ)}
    {V : Submodule ℂ (ι → ℂ)} [FiniteDimensional ℂ V] (hle : V ≤ D)
    (hneg : ∀ u ∈ V, u ≠ 0 → Q u < 0) : (Module.finrank ℂ V : ℕ∞) ≤ formIndex Q D := by
  unfold formIndex
  exact le_iSup₂_of_le V ⟨hle, hneg⟩ (le_iSup_of_le ‹_› le_rfl)

/-- **Index lower bound from a negative-definite finite family.**  If every nonzero combination of
`v : Fin n → (ι → ℂ)` (all in `D`) has `Q < 0`, then `n ≤ formIndex Q D`. -/
theorem formIndex_ge_of_neg {Q : (ι → ℂ) → ℝ} {D : Submodule ℂ (ι → ℂ)} (hQ0 : Q 0 = 0)
    {n : ℕ} (v : Fin n → (ι → ℂ)) (hv : ∀ i, v i ∈ D)
    (hneg : ∀ c : Fin n → ℂ, c ≠ 0 → Q (∑ i, c i • v i) < 0) :
    (n : ℕ∞) ≤ formIndex Q D := by
  -- linear independence
  have hli : LinearIndependent ℂ v := by
    rw [Fintype.linearIndependent_iff]
    intro g hg
    by_contra hcon
    have hg0 : g ≠ 0 := fun h => hcon fun i => by rw [h]; rfl
    have hlt : Q (∑ i, g i • v i) < 0 := hneg g hg0
    rw [hg, hQ0] at hlt
    exact lt_irrefl _ hlt
  set V : Submodule ℂ (ι → ℂ) := Submodule.span ℂ (Set.range v) with hVdef
  have hVfin : FiniteDimensional ℂ V := FiniteDimensional.span_of_finite ℂ (Set.finite_range v)
  have hfr : Module.finrank ℂ V = n := by
    rw [hVdef, finrank_span_eq_card hli, Fintype.card_fin]
  have hle : V ≤ D := by
    rw [hVdef, Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    exact hv i
  have hVneg : ∀ u ∈ V, u ≠ 0 → Q u < 0 := by
    intro u hu hune
    obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).mp hu
    refine hneg c fun h => hune ?_
    rw [h]; simp
  have := finrank_le_formIndex (Q := Q) (D := D) (V := V) hle hVneg
  rwa [hfr] at this

/-! ### Finite sesquilinear expansion on bounded differentiable families -/

/-- `u` is differentiable and bounded (value and gradient) on the disk. -/
def DiskNice (u : ℂ → ℂ) : Prop :=
  (∀ w ∈ disk, DifferentiableAt ℝ u w) ∧
    ∃ M : ℝ, ∀ w ∈ disk, ‖u w‖ ≤ M ∧ ‖fderiv ℝ u w‖ ≤ M

lemma DiskNice.differentiableAt {u : ℂ → ℂ} (hu : DiskNice u) {w : ℂ} (hw : w ∈ disk) :
    DifferentiableAt ℝ u w := hu.1 w hw

lemma DiskNice.continuousOn {u : ℂ → ℂ} (hu : DiskNice u) : ContinuousOn u disk :=
  fun w hw => (hu.1 w hw).continuousAt.continuousWithinAt

lemma diskNice_smul {c : ℂ} {u : ℂ → ℂ} (hu : DiskNice u) : DiskNice (fun w => c • u w) := by
  obtain ⟨hd, M, hM⟩ := hu
  refine ⟨fun w hw => (hd w hw).const_smul c, ‖c‖ * M, fun w hw => ?_⟩
  have hb := hM w hw
  have hf : fderiv ℝ (fun w => c • u w) w = c • fderiv ℝ (u) w :=
    fderiv_fun_const_smul (hd w hw) c
  constructor
  · simp only [smul_eq_mul, norm_mul]; exact mul_le_mul_of_nonneg_left hb.1 (norm_nonneg _)
  · rw [hf, norm_smul]; exact mul_le_mul_of_nonneg_left hb.2 (norm_nonneg _)

lemma diskNice_sum {n : ℕ} {u : Fin n → ℂ → ℂ} (hu : ∀ i, DiskNice (u i)) :
    DiskNice (fun w => ∑ i, u i w) := by
  refine ⟨fun w hw => DifferentiableAt.fun_sum fun i _ => (hu i).1 w hw, ?_⟩
  choose M hM using fun i => (hu i).2
  refine ⟨∑ i, M i, fun w hw => ?_⟩
  have hfd : fderiv ℝ (fun w => ∑ i, u i w) w = ∑ i, fderiv ℝ (u i) w :=
    fderiv_fun_sum fun i _ => (hu i).1 w hw
  constructor
  · exact le_trans (norm_sum_le _ _) (Finset.sum_le_sum fun i _ => (hM i w hw).1)
  · rw [hfd]
    exact le_trans (norm_sum_le _ _) (Finset.sum_le_sum fun i _ => (hM i w hw).2)

/-- The gradient cross density of two `DiskNice` functions is integrable on the disk. -/
lemma integrableOn_gradInner_nice {u v : ℂ → ℂ} (hu : DiskNice u) (hv : DiskNice v) :
    IntegrableOn (gradInner u v) disk := by
  obtain ⟨Mu, hMu⟩ := hu.2
  obtain ⟨Mv, hMv⟩ := hv.2
  exact integrableOn_gradInner_bounded (Df := Mu) (Dg := Mv)
    (fun w hw => (hMu w hw).2) (fun w hw => (hMv w hw).2)

lemma integrableOn_pot_nice (hk : 2 ≤ k) {u v : ℂ → ℂ} (hu : DiskNice u) (hv : DiskNice v) :
    IntegrableOn (fun w => (potV k w : ℂ) * (starRingEnd ℂ) (u w) * v w) disk := by
  obtain ⟨Mu, hMu⟩ := hu.2
  obtain ⟨Mv, hMv⟩ := hv.2
  exact integrableOn_pot hk (DiskNice.continuousOn hu) (DiskNice.continuousOn hv)
    (fun w hw => (hMu w hw).1) (fun w hw => (hMv w hw).1)

/-- Pointwise gradient-density sesquilinear expansion on the disk. -/
lemma gradInner_finsum_pt {n : ℕ} (a b : Fin n → ℂ) {u : Fin n → ℂ → ℂ}
    (hu : ∀ i, DiskNice (u i)) {w : ℂ} (hw : w ∈ disk) :
    gradInner (fun z => ∑ i, a i • u i z) (fun z => ∑ j, b j • u j z) w
      = ∑ i, ∑ j, (starRingEnd ℂ) (a i) * b j * gradInner (u i) (u j) w := by
  have hfa : fderiv ℝ (fun z => ∑ i, a i • u i z) w = ∑ i, a i • fderiv ℝ (u i) w := by
    rw [fderiv_fun_sum (A := fun i z => a i • u i z)
      fun i _ => ((hu i).1 w hw).const_smul (a i)]
    exact Finset.sum_congr rfl fun i _ => fderiv_fun_const_smul ((hu i).1 w hw) _
  have hfb : fderiv ℝ (fun z => ∑ j, b j • u j z) w = ∑ j, b j • fderiv ℝ (u j) w := by
    rw [fderiv_fun_sum (A := fun j z => b j • u j z)
      fun j _ => ((hu j).1 w hw).const_smul (b j)]
    exact Finset.sum_congr rfl fun j _ => fderiv_fun_const_smul ((hu j).1 w hw) _
  unfold gradInner
  rw [hfa, hfb]
  simp only [sum_apply, smul_apply, smul_eq_mul, map_sum, map_mul, Finset.sum_mul_sum]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

lemma potDens_finsum_pt {n : ℕ} (a b : Fin n → ℂ) (u : Fin n → ℂ → ℂ) (w : ℂ) :
    (potV k w : ℂ) * (starRingEnd ℂ) (∑ i, a i • u i w) * (∑ j, b j • u j w)
      = ∑ i, ∑ j, (starRingEnd ℂ) (a i) * b j
          * ((potV k w : ℂ) * (starRingEnd ℂ) (u i w) * u j w) := by
  simp only [smul_eq_mul, map_sum, map_mul, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

/-- Finite sesquilinear expansion of `Bd` on a `DiskNice` family. -/
theorem Bd_finsum (hk : 2 ≤ k) {n : ℕ} (a b : Fin n → ℂ) {u : Fin n → ℂ → ℂ}
    (hu : ∀ i, DiskNice (u i)) :
    Bd k (fun w => ∑ i, a i • u i w) (fun w => ∑ j, b j • u j w)
      = ∑ i, ∑ j, (starRingEnd ℂ) (a i) * b j * Bd k (u i) (u j) := by
  have h0 : ∀ᵐ w ∂(volume.restrict disk), w ∈ disk :=
    (ae_restrict_iff' measurableSet_disk).mpr (Eventually.of_forall fun _ h => h)
  have hg : ∫ w in disk, gradInner (fun z => ∑ i, a i • u i z) (fun z => ∑ j, b j • u j z) w
      = ∑ i, ∑ j, (starRingEnd ℂ) (a i) * b j * ∫ w in disk, gradInner (u i) (u j) w := by
    rw [integral_congr_ae (g := fun w => ∑ i, ∑ j,
        (starRingEnd ℂ) (a i) * b j * gradInner (u i) (u j) w)
      (by filter_upwards [h0] with w hw using gradInner_finsum_pt a b hu hw)]
    rw [integral_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ =>
      (integrableOn_gradInner_nice (hu i) (hu j)).const_mul _]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [integral_finsetSum _ fun j _ =>
      (integrableOn_gradInner_nice (hu i) (hu j)).const_mul _]
    exact Finset.sum_congr rfl fun j _ => integral_const_mul _ _
  have hp : ∫ w in disk, (potV k w : ℂ) * (starRingEnd ℂ) ((fun z => ∑ i, a i • u i z) w)
        * (fun z => ∑ j, b j • u j z) w
      = ∑ i, ∑ j, (starRingEnd ℂ) (a i) * b j
          * ∫ w in disk, (potV k w : ℂ) * (starRingEnd ℂ) (u i w) * u j w := by
    simp only []
    rw [integral_congr_ae (g := fun w => ∑ i, ∑ j, (starRingEnd ℂ) (a i) * b j
        * ((potV k w : ℂ) * (starRingEnd ℂ) (u i w) * u j w))
      (Eventually.of_forall fun w => potDens_finsum_pt a b u w)]
    rw [integral_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ =>
      (integrableOn_pot_nice hk (hu i) (hu j)).const_mul _]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [integral_finsetSum _ fun j _ =>
      (integrableOn_pot_nice hk (hu i) (hu j)).const_mul _]
    exact Finset.sum_congr rfl fun j _ => integral_const_mul _ _
  unfold Bd
  rw [hg, hp, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun j _ => by ring

/-! ### `DiskNice` for the modes and their cutoffs -/

/-- A `C^∞` function on `ℂ` is bounded (value and gradient) on the disk. -/
lemma diskNice_of_contDiff {u : ℂ → ℂ} (hu : ContDiff ℝ ∞ u) : DiskNice u := by
  refine ⟨fun w _ => (hu.differentiable (by simp)) w, ?_⟩
  obtain ⟨Mv, hMv⟩ := (isCompact_closedBall (0 : ℂ) 1).exists_bound_of_continuousOn
    hu.continuous.norm.continuousOn
  obtain ⟨Md, hMd⟩ := (isCompact_closedBall (0 : ℂ) 1).exists_bound_of_continuousOn
    (f := fun w => fderiv ℝ u w) (hu.continuous_fderiv (by simp)).continuousOn
  refine ⟨max Mv Md, fun w hw => ?_⟩
  have hwc : w ∈ Metric.closedBall (0 : ℂ) 1 := Metric.ball_subset_closedBall hw
  refine ⟨?_, ?_⟩
  · exact le_trans (by simpa using hMv w hwc) (le_max_left _ _)
  · exact le_trans (hMd w hwc) (le_max_right _ _)

/-- The modes are `DiskNice`. -/
lemma diskNice_modeU (hk : 1 ≤ k) (ℓ : ℕ) : DiskNice (modeU k ℓ) :=
  diskNice_of_contDiff (modeU_contDiff hk ℓ)

/-- `cutMul` of a `DiskNice` function by a bounded-gradient `C^∞` cutoff with values in `[0,1]` is
`DiskNice`. -/
lemma diskNice_cutMul {χ : ℂ → ℝ} (hχ : ContDiff ℝ ∞ χ) (hχ0 : ∀ w, 0 ≤ χ w)
    (hχ1 : ∀ w, χ w ≤ 1) {u : ℂ → ℂ} (hu : DiskNice u) : DiskNice (cutMul χ u) := by
  obtain ⟨hud, Mu, hMu⟩ := hu
  have hχd : ∀ w, DifferentiableAt ℝ χ w := fun w => (hχ.differentiable (by simp)) w
  obtain ⟨Mχ, hMχ⟩ := (isCompact_closedBall (0 : ℂ) 1).exists_bound_of_continuousOn
    (f := fun w => fderiv ℝ χ w) (hχ.continuous_fderiv (by simp)).continuousOn
  refine ⟨fun w hw => (hasFDerivAt_cutMul (hχd w) (hud w hw)).differentiableAt, Mu + Mu * Mχ,
    fun w hw => ?_⟩
  have hwc : w ∈ Metric.closedBall (0 : ℂ) 1 := Metric.ball_subset_closedBall hw
  have hb := hMu w hw
  have hMu0 : 0 ≤ Mu := le_trans (norm_nonneg _) hb.1
  refine ⟨?_, ?_⟩
  · -- value: |χ| |u| ≤ 1·Mu ≤ Mu + Mu Mχ
    unfold cutMul
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hχ0 w)]
    have hχu : χ w * ‖u w‖ ≤ Mu := le_trans (mul_le_of_le_one_left (norm_nonneg _) (hχ1 w)) hb.1
    have : (0 : ℝ) ≤ Mu * Mχ := by
      have := le_trans (norm_nonneg _) (hMχ w hwc); positivity
    linarith
  · -- gradient: ‖χ ∇u + u ∇χ‖ ≤ Mu + Mu Mχ
    rw [(hasFDerivAt_cutMul (hχd w) (hud w hw)).fderiv]
    refine le_trans (norm_add_le _ _) ?_
    rw [norm_smul, norm_smul]
    have t1 : ‖(χ w : ℂ)‖ * ‖fderiv ℝ u w‖ ≤ Mu := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hχ0 w)]
      exact le_trans (mul_le_of_le_one_left (norm_nonneg _) (hχ1 w)) hb.2
    have t2 : ‖u w‖ * ‖Complex.ofRealCLM.comp (fderiv ℝ χ w)‖ ≤ Mu * Mχ := by
      apply mul_le_mul hb.1 _ (norm_nonneg _) hMu0
      have hcomp : ‖Complex.ofRealCLM.comp (fderiv ℝ χ w)‖ ≤ ‖fderiv ℝ χ w‖ := by
        refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun v => ?_
        simp only [ContinuousLinearMap.comp_apply, Complex.ofRealCLM_apply, Complex.norm_real,
          Real.norm_eq_abs]
        exact (fderiv ℝ χ w).le_opNorm v
      exact le_trans hcomp (hMχ w hwc)
    linarith

/-! ### Per-mode disk bounds and combination bounds -/

/-- A single bound on `modeU k ℓ` (value and gradient) over the disk. -/
def modeBd (k ℓ : ℕ) (hk : 2 ≤ k) : ℝ := (diskNice_modeU (k := k) (by omega) ℓ).2.choose

lemma modeBd_spec {k : ℕ} (hk : 2 ≤ k) (ℓ : ℕ) {w : ℂ} (hw : w ∈ disk) :
    ‖modeU k ℓ w‖ ≤ modeBd k ℓ hk ∧ ‖fderiv ℝ (modeU k ℓ) w‖ ≤ modeBd k ℓ hk :=
  (diskNice_modeU (k := k) (by omega) ℓ).2.choose_spec w hw

lemma modeBd_nonneg {k : ℕ} (hk : 2 ≤ k) (ℓ : ℕ) : 0 ≤ modeBd k ℓ hk :=
  le_trans (norm_nonneg _) (modeBd_spec hk ℓ (by simp [mem_disk_iff] : (0:ℂ) ∈ disk)).1

/-- `modeSum` is differentiable everywhere (each mode is `C^∞` on `ℂ`). -/
lemma differentiableAt_modeSum (hk : 2 ≤ k) (S : Finset ℕ) (c : ℕ → ℂ) (w : ℂ) :
    DifferentiableAt ℝ (modeSum k S c) w := by
  unfold modeSum
  exact DifferentiableAt.fun_sum fun ℓ _ =>
    (((modeU_contDiff (by omega) ℓ).differentiable (by simp)) w).const_smul (c ℓ)

/-- The uniform combination bound `R(c) = ∑_{ℓ∈S} ‖c ℓ‖ · modeBd ℓ`. -/
def combBd (k : ℕ) (hk : 2 ≤ k) (S : Finset ℕ) (c : ℕ → ℂ) : ℝ :=
  ∑ ℓ ∈ S, ‖c ℓ‖ * modeBd k ℓ hk

lemma combBd_nonneg {k : ℕ} (hk : 2 ≤ k) (S : Finset ℕ) (c : ℕ → ℂ) :
    0 ≤ combBd k hk S c :=
  Finset.sum_nonneg fun ℓ _ => mul_nonneg (norm_nonneg _) (modeBd_nonneg hk ℓ)

lemma norm_modeSum_le {k : ℕ} (hk : 2 ≤ k) (S : Finset ℕ) (c : ℕ → ℂ) {w : ℂ} (hw : w ∈ disk) :
    ‖modeSum k S c w‖ ≤ combBd k hk S c := by
  unfold modeSum combBd
  refine le_trans (norm_sum_le _ _) (Finset.sum_le_sum fun ℓ _ => ?_)
  rw [smul_eq_mul, norm_mul]
  exact mul_le_mul_of_nonneg_left (modeBd_spec hk ℓ hw).1 (norm_nonneg _)

lemma norm_fderiv_modeSum_le {k : ℕ} (hk : 2 ≤ k) (S : Finset ℕ) (c : ℕ → ℂ) {w : ℂ}
    (hw : w ∈ disk) : ‖fderiv ℝ (modeSum k S c) w‖ ≤ combBd k hk S c := by
  have hfd : fderiv ℝ (modeSum k S c) w = ∑ ℓ ∈ S, c ℓ • fderiv ℝ (modeU k ℓ) w := by
    unfold modeSum
    rw [fderiv_fun_sum (A := fun ℓ z => c ℓ • modeU k ℓ z)
      fun ℓ _ => ((modeU_contDiff (by omega) ℓ).differentiable (by simp) w).const_smul (c ℓ)]
    exact Finset.sum_congr rfl fun ℓ _ =>
      fderiv_fun_const_smul ((modeU_contDiff (by omega) ℓ).differentiable (by simp) w) _
  rw [hfd]
  unfold combBd
  refine le_trans (norm_sum_le _ _) (Finset.sum_le_sum fun ℓ _ => ?_)
  rw [norm_smul]
  exact mul_le_mul_of_nonneg_left (modeBd_spec hk ℓ hw).2 (norm_nonneg _)

/-- Cauchy–Schwarz: `combBd² ≤ (∑ ‖c ℓ‖²)·(∑ modeBd ℓ²)`. -/
lemma combBd_sq_le {k : ℕ} (hk : 2 ≤ k) (S : Finset ℕ) (c : ℕ → ℂ) :
    combBd k hk S c ^ 2 ≤ (∑ ℓ ∈ S, ‖c ℓ‖ ^ 2) * (∑ ℓ ∈ S, modeBd k ℓ hk ^ 2) := by
  calc combBd k hk S c ^ 2 = (∑ ℓ ∈ S, ‖c ℓ‖ * modeBd k ℓ hk) ^ 2 := rfl
    _ ≤ _ := Finset.sum_mul_sq_le_sq_mul_sq S (fun ℓ => ‖c ℓ‖) (fun ℓ => modeBd k ℓ hk)

/-! ### The Gram perturbation: negativity for small `ε` -/

/-- `∑_{ℓ∈S} c ℓ • cutMul χ (modeU ℓ) = cutMul χ (modeSum S c)` as functions. -/
lemma sum_smul_cutMul_eq (χ : ℂ → ℝ) (S : Finset ℕ) (c : ℕ → ℂ) :
    (∑ ℓ ∈ S, c ℓ • cutMul χ (modeU k ℓ)) = cutMul χ (modeSum k S c) := by
  funext w
  simp only [Finset.sum_apply, Pi.smul_apply, cutMul, modeSum, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun ℓ _ => by ring

/-- `Qd` of the cut-off combination is bounded by the mode diagonal plus the cutoff error. -/
lemma Qd_cutMul_modeSum_le (hk : 2 ≤ k) (S : Finset ℕ) (c : ℕ → ℂ) {ε δ : ℝ}
    (h0 : 0 < ε) (h1 : ε < 1) (hδ : 0 < δ) :
    Qd k (cutMul (cutP k ε) (modeSum k S c))
      ≤ Qd k (modeSum k S c)
        + (2 * (combBd k hk S c) ^ 2 + 8 * ((k : ℝ) - 1) ^ 2 * (combBd k hk S c) ^ 2)
            * (volume : Measure ℂ).real (disk ∩ Uε k ε)
          + (2 * (combBd k hk S c) ^ 2) * (δ * Real.pi)
          + ((2 * (combBd k hk S c) ^ 2) / (2 * δ) + (combBd k hk S c) ^ 2)
              * ∫ w in disk, gradSq (cutPC k ε) w := by
  set R := combBd k hk S c with hR
  have hf : ∀ w ∈ disk, DifferentiableAt ℝ (modeSum k S c) w :=
    fun w _ => differentiableAt_modeSum hk S c w
  have hbd := Bd_cutoff_bound (k := k) hk h0 h1 hδ (f := modeSum k S c) (g := modeSum k S c)
    (Mf := R) (Df := R) (Mg := R) (Dg := R)
    hf (fun w hw => norm_modeSum_le hk S c hw) (fun w hw => norm_fderiv_modeSum_le hk S c hw)
    hf (fun w hw => norm_modeSum_le hk S c hw) (fun w hw => norm_fderiv_modeSum_le hk S c hw)
  rw [Bd_self_eq_Qd hk, Bd_self_eq_Qd hk, ← Complex.ofReal_sub] at hbd
  rw [Complex.norm_real, Real.norm_eq_abs] at hbd
  have h2 := (abs_le.mp hbd).2
  have key : (2 * (R * R) + 8 * ((k : ℝ) - 1) ^ 2 * (R * R))
        * (volume : Measure ℂ).real (disk ∩ Uε k ε) + (R * R + R * R) * (δ * Real.pi)
        + ((R * R + R * R) / (2 * δ) + R * R) * ∫ w in disk, gradSq (cutPC k ε) w
      = (2 * R ^ 2 + 8 * ((k : ℝ) - 1) ^ 2 * R ^ 2)
          * (volume : Measure ℂ).real (disk ∩ Uε k ε) + 2 * R ^ 2 * (δ * Real.pi)
        + (2 * R ^ 2 / (2 * δ) + R ^ 2) * ∫ w in disk, gradSq (cutPC k ε) w := by ring
  rw [key] at h2
  linarith [h2]

/-- The explicit error-bound function (with `δ` fixed), dominating the cutoff error. -/
private def bndFun (k : ℕ) (N Mψ' δ : ℝ) (ε : ℝ) : ℝ :=
  (2 + 8 * ((k : ℝ) - 1) ^ 2) * (N * (Real.pi * ε ^ 2)) + 2 * (δ * Real.pi)
    + (1 / δ + 1) * (4 * Real.pi * N ^ 2 * Mψ' ^ 2 * (Lε ε)⁻¹)

/-- **The Gram perturbation.**  For a finite set `S` of positive-frequency modes with negative symbols,
every sufficiently small positive scale `ε` preserves strict negativity of all
combinations whose coefficients are nonzero somewhere on `S`. -/
theorem eventually_eps_neg (hk : 2 ≤ k) (S : Finset ℕ) (hS1 : ∀ ℓ ∈ S, 1 ≤ ℓ)
    (hSneg : ∀ ℓ ∈ S, KsIndex.Radial.sigma k ℓ < 0) :
    ∀ᶠ ε : ℝ in 𝓝[>] (0:ℝ), 0 < ε ∧ ε < 1 ∧ ∀ c : ℕ → ℂ, (∃ ℓ ∈ S, c ℓ ≠ 0) →
      Qd k (∑ ℓ ∈ S, c ℓ • cutMul (cutP k ε) (modeU k ℓ)) < 0 := by
  have hev1 : ∀ᶠ ε in 𝓝[>] (0:ℝ), ε < 1 :=
    (Filter.eventually_of_mem (Iio_mem_nhds (show (0:ℝ) < 1 by norm_num)) fun x hx => hx).filter_mono
      nhdsWithin_le_nhds
  have hev0 : ∀ᶠ ε in 𝓝[>] (0:ℝ), (0:ℝ) < ε := eventually_mem_nhdsWithin.mono fun _ h => h
  rcases S.eq_empty_or_nonempty with rfl | hSne
  · filter_upwards [hev1, hev0] with ε hεlt hε0
    exact ⟨hε0, hεlt, fun c hc => by simp at hc⟩
  have hπ : 0 < Real.pi := Real.pi_pos
  -- diagonal bounded away from 0
  have hdiag : ∀ ℓ ∈ S, 2 * Real.pi * ((ℓ : ℝ) ^ 2 * KsIndex.Radial.sigma k ℓ) < 0 := by
    intro ℓ hℓ
    have h2 : (0 : ℝ) < (ℓ : ℝ) ^ 2 := by
      have := hS1 ℓ hℓ; positivity
    have hmul : (ℓ : ℝ) ^ 2 * KsIndex.Radial.sigma k ℓ < 0 :=
      mul_neg_of_pos_of_neg h2 (hSneg ℓ hℓ)
    have : (0:ℝ) < 2 * Real.pi := by positivity
    exact mul_neg_of_pos_of_neg this hmul
  obtain ⟨ℓ₀, hℓ₀S, hmin⟩ := S.exists_min_image
    (fun ℓ => -(2 * Real.pi * ((ℓ : ℝ) ^ 2 * KsIndex.Radial.sigma k ℓ))) hSne
  set m : ℝ := -(2 * Real.pi * ((ℓ₀ : ℝ) ^ 2 * KsIndex.Radial.sigma k ℓ₀)) with hm
  have hm0 : 0 < m := by rw [hm, neg_pos]; exact hdiag ℓ₀ hℓ₀S
  have hmbound : ∀ ℓ ∈ S, 2 * Real.pi * ((ℓ : ℝ) ^ 2 * KsIndex.Radial.sigma k ℓ) ≤ -m := by
    intro ℓ hℓ; have := hmin ℓ hℓ; simp only [hm]; linarith
  set P : ℝ := ∑ ℓ ∈ S, modeBd k ℓ hk ^ 2 with hP
  have hP0 : 0 ≤ P := Finset.sum_nonneg fun ℓ _ => sq_nonneg _
  set N : ℝ := ((pF k).card : ℝ) with hN
  have hN0 : 0 ≤ N := by positivity
  set δ : ℝ := m / (4 * Real.pi * P + 1) with hδdef
  have hd1 : (0:ℝ) < 4 * Real.pi * P + 1 := by positivity
  have hδ0 : 0 < δ := by rw [hδdef]; positivity
  -- the ε→0 limit value `2δπ`, times `P`, still below `m`
  have hlim_neg : -m + P * (2 * (δ * Real.pi)) < 0 := by
    have hkey : P * (2 * (δ * Real.pi)) < m := by
      have heq : P * (2 * (δ * Real.pi)) = 2 * Real.pi * P * m / (4 * Real.pi * P + 1) := by
        rw [hδdef]; field_simp; try ring
      rw [heq, div_lt_iff₀ hd1]
      nlinarith [hm0, hP0, hπ, mul_nonneg (mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 2)
        hπ.le) hP0) hm0.le]
    linarith [hkey]
  -- the bound function tends to `2δπ` as `ε → 0⁺`
  have hsq : Filter.Tendsto (fun ε : ℝ => ε ^ 2) (𝓝[>] (0:ℝ)) (𝓝 0) := by
    have h : Filter.Tendsto (fun ε : ℝ => ε ^ 2) (𝓝 (0:ℝ)) (𝓝 ((0:ℝ) ^ 2)) :=
      (continuous_pow 2).tendsto 0
    simpa using h.mono_left nhdsWithin_le_nhds
  have hinv : Filter.Tendsto (fun ε : ℝ => (Lε ε)⁻¹) (𝓝[>] (0:ℝ)) (𝓝 0) := by
    apply Filter.Tendsto.inv_tendsto_atTop
    have hL : Filter.Tendsto (fun ε : ℝ => Lε ε) (𝓝[>] (0:ℝ)) Filter.atTop := by
      simp only [Lε]
      first
        | exact tendsto_neg_atTop_iff.mpr Real.tendsto_log_nhdsGT_zero
        | exact Filter.tendsto_neg_atTop_iff.mpr Real.tendsto_log_nhdsGT_zero
        | exact Real.tendsto_log_nhdsGT_zero.neg_atBot
    exact hL
  have hlim : Filter.Tendsto (fun ε => bndFun k N Mψ δ ε) (𝓝[>] (0:ℝ))
      (𝓝 (2 * (δ * Real.pi))) := by
    have key : Filter.Tendsto (fun ε => bndFun k N Mψ δ ε) (𝓝[>] (0:ℝ))
        (𝓝 ((2 + 8 * ((k : ℝ) - 1) ^ 2) * (N * (Real.pi * 0)) + 2 * (δ * Real.pi)
          + (1 / δ + 1) * (4 * Real.pi * N ^ 2 * Mψ ^ 2 * 0))) := by
      simp only [bndFun]
      exact (((tendsto_const_nhds).mul (tendsto_const_nhds.mul (tendsto_const_nhds.mul hsq))).add
        tendsto_const_nhds).add (tendsto_const_nhds.mul (tendsto_const_nhds.mul hinv))
    have heq : (2 + 8 * ((k : ℝ) - 1) ^ 2) * (N * (Real.pi * 0)) + 2 * (δ * Real.pi)
        + (1 / δ + 1) * (4 * Real.pi * N ^ 2 * Mψ ^ 2 * 0) = 2 * (δ * Real.pi) := by ring
    rwa [heq] at key
  -- extract a good ε
  have hcont : Filter.Tendsto (fun ε => -m + P * bndFun k N Mψ δ ε) (𝓝[>] (0:ℝ))
      (𝓝 (-m + P * (2 * (δ * Real.pi)))) :=
    (tendsto_const_nhds).add (tendsto_const_nhds.mul hlim)
  have hev : ∀ᶠ ε in 𝓝[>] (0:ℝ), -m + P * bndFun k N Mψ δ ε < 0 :=
    hcont.eventually_lt_const hlim_neg
  filter_upwards [hev, hev1, hev0] with ε hεBnd hεlt hε0
  refine ⟨hε0, hεlt, fun c hc => ?_⟩
  rw [sum_smul_cutMul_eq]
  set T : ℝ := ∑ ℓ ∈ S, ‖c ℓ‖ ^ 2 with hT
  have hTpos : 0 < T := by
    obtain ⟨ℓ, hℓS, hcℓ⟩ := hc
    exact hT ▸ Finset.sum_pos' (fun ℓ _ => sq_nonneg _) ⟨ℓ, hℓS, by positivity⟩

  -- the main bound
  have hstep : Qd k (cutMul (cutP k ε) (modeSum k S c)) ≤ T * (-m + P * bndFun k N Mψ δ ε) := by
    set R := combBd k hk S c with hRdef
    have hR2 : R ^ 2 ≤ T * P := by rw [hRdef, hT, hP]; exact combBd_sq_le hk S c
    have hR0 : 0 ≤ R ^ 2 := sq_nonneg _
    have hQms : Qd k (modeSum k S c) ≤ -m * T := by
      rw [Qd_modeSum hk S hS1 c, hT, Finset.mul_sum]
      refine Finset.sum_le_sum fun ℓ hℓ => ?_
      have := hmbound ℓ hℓ
      have hcnn : (0:ℝ) ≤ ‖c ℓ‖ ^ 2 := sq_nonneg _
      calc ‖c ℓ‖ ^ 2 * (2 * Real.pi * ((ℓ : ℝ) ^ 2 * KsIndex.Radial.sigma k ℓ))
          ≤ ‖c ℓ‖ ^ 2 * (-m) := mul_le_mul_of_nonneg_left this hcnn
        _ = -m * ‖c ℓ‖ ^ 2 := by ring
    have hUfin : volume (Uε k ε) ≠ ⊤ := by
      refine ne_top_of_le_ne_top ?_ (measure_biUnion_finset_le (pF k) (fun p => Metric.ball p ε))
      refine (ENNReal.sum_lt_top.mpr fun p _ => ?_).ne
      rw [Complex.volume_ball]; exact ENNReal.mul_lt_top (by finiteness) (by finiteness)
    have harea : (volume : Measure ℂ).real (disk ∩ Uε k ε) ≤ N * (Real.pi * ε ^ 2) :=
      le_trans (measureReal_mono Set.inter_subset_right hUfin) (by rw [hN]; exact volume_real_Uε_le k hε0)
    have henergy : ∫ w in disk, gradSq (cutPC k ε) w ≤ 4 * Real.pi * N ^ 2 * Mψ ^ 2 / Lε ε := by
      rw [hN]; exact_mod_cast energy_cutP_le k hε0 hεlt
    have hLε : 0 < Lε ε := Lε_pos hε0 hεlt
    -- the cutoff-error bound in factored form
    have herr : (2 * R ^ 2 + 8 * ((k : ℝ) - 1) ^ 2 * R ^ 2)
          * (volume : Measure ℂ).real (disk ∩ Uε k ε) + 2 * R ^ 2 * (δ * Real.pi)
          + (2 * R ^ 2 / (2 * δ) + R ^ 2) * ∫ w in disk, gradSq (cutPC k ε) w
        ≤ R ^ 2 * bndFun k N Mψ δ ε := by
      have hc1 : (0:ℝ) ≤ 2 + 8 * ((k : ℝ) - 1) ^ 2 := by positivity
      have hc2 : (0:ℝ) ≤ 1 / δ + 1 := by positivity
      have hE0 : (0:ℝ) ≤ 4 * Real.pi * N ^ 2 * Mψ ^ 2 / Lε ε := by positivity
      have hEcoef : (0:ℝ) ≤ 4 * Real.pi * N ^ 2 * Mψ ^ 2 := by positivity
      have hfac : (2 * R ^ 2 + 8 * ((k : ℝ) - 1) ^ 2 * R ^ 2)
            * (volume : Measure ℂ).real (disk ∩ Uε k ε) + 2 * R ^ 2 * (δ * Real.pi)
            + (2 * R ^ 2 / (2 * δ) + R ^ 2) * ∫ w in disk, gradSq (cutPC k ε) w
          = R ^ 2 * ((2 + 8 * ((k : ℝ) - 1) ^ 2)
              * (volume : Measure ℂ).real (disk ∩ Uε k ε) + 2 * (δ * Real.pi)
            + (1 / δ + 1) * ∫ w in disk, gradSq (cutPC k ε) w) := by
        have hδne : (δ:ℝ) ≠ 0 := hδ0.ne'
        field_simp
        try ring
      rw [hfac]
      apply mul_le_mul_of_nonneg_left _ hR0
      simp only [bndFun]
      have h4 : (1 / δ + 1) * ∫ w in disk, gradSq (cutPC k ε) w
          ≤ (1 / δ + 1) * (4 * Real.pi * N ^ 2 * Mψ ^ 2 * (Lε ε)⁻¹) := by
        apply mul_le_mul_of_nonneg_left _ hc2
        rw [div_eq_mul_inv] at henergy
        linarith [henergy]
      have h3 : (2 + 8 * ((k : ℝ) - 1) ^ 2) * (volume : Measure ℂ).real (disk ∩ Uε k ε)
          ≤ (2 + 8 * ((k : ℝ) - 1) ^ 2) * (N * (Real.pi * ε ^ 2)) :=
        mul_le_mul_of_nonneg_left harea hc1
      linarith [h3, h4]
    calc Qd k (cutMul (cutP k ε) (modeSum k S c))
        ≤ Qd k (modeSum k S c)
          + ((2 * R ^ 2 + 8 * ((k : ℝ) - 1) ^ 2 * R ^ 2)
              * (volume : Measure ℂ).real (disk ∩ Uε k ε) + 2 * R ^ 2 * (δ * Real.pi)
            + (2 * R ^ 2 / (2 * δ) + R ^ 2) * ∫ w in disk, gradSq (cutPC k ε) w) := by
          have := Qd_cutMul_modeSum_le hk S c hε0 hεlt hδ0
          simp only [hRdef] at this ⊢; linarith [this]
      _ ≤ -m * T + R ^ 2 * bndFun k N Mψ δ ε := by linarith [hQms, herr]
      _ ≤ -m * T + (T * P) * bndFun k N Mψ δ ε := by
          have hbnd0 : 0 ≤ bndFun k N Mψ δ ε := by
            simp only [bndFun]
            have : (0:ℝ) ≤ (Lε ε)⁻¹ := by positivity
            have h1 : (0:ℝ) ≤ (2 + 8 * ((k : ℝ) - 1) ^ 2) * (N * (Real.pi * ε ^ 2)) := by positivity
            have h2 : (0:ℝ) ≤ (1 / δ + 1) * (4 * Real.pi * N ^ 2 * Mψ ^ 2 * (Lε ε)⁻¹) := by
              positivity
            have h3 : (0:ℝ) ≤ 2 * (δ * Real.pi) := by positivity
            linarith
          have := mul_le_mul_of_nonneg_right hR2 hbnd0
          linarith [this]
      _ = T * (-m + P * bndFun k N Mψ δ ε) := by ring
  calc Qd k (cutMul (cutP k ε) (modeSum k S c))
      ≤ T * (-m + P * bndFun k N Mψ δ ε) := hstep
    _ < 0 := mul_neg_of_pos_of_neg hTpos hεBnd


/-- **The Gram perturbation** (existential form). -/
theorem exists_eps_neg (hk : 2 ≤ k) (S : Finset ℕ) (hS1 : ∀ ℓ ∈ S, 1 ≤ ℓ)
    (hSneg : ∀ ℓ ∈ S, KsIndex.Radial.sigma k ℓ < 0) :
    ∃ ε : ℝ, 0 < ε ∧ ε < 1 ∧ ∀ c : ℕ → ℂ, (∃ ℓ ∈ S, c ℓ ≠ 0) →
      Qd k (∑ ℓ ∈ S, c ℓ • cutMul (cutP k ε) (modeU k ℓ)) < 0 :=
  (eventually_eps_neg hk S hS1 hSneg).exists

end KsIndex.FormIndex
