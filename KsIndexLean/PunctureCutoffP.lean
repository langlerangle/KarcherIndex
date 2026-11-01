module

/-
KsIndexLean — Product cutoffs over the puncture set.

`cutP k ε w = ∏_{p ∈ pF k} cut1 ε p w`, where `pF k` is the finite set of
`2k`-th roots of `−1`. For `k ≥ 1` this is the surface puncture set.
For `0 < ε < 1`, the product is zero within `ε²` of a puncture, one at
points at least `ε` from every puncture, and smooth on `ℂ`, with values
in `[0,1]`. Unit rotations satisfying `a^(2*k) = 1` preserve it when `k ≥ 1`.

Writing `N = (pF k).card ≤ 2*k`, the Dirichlet energy satisfies
`∫_disk gradSq (cutPC k ε) ≤ 4*π*N²*Mψ² / log(1/ε)` for `0 < ε < 1`.
The proof bounds the derivative norm of the product by the sum of the
individual derivative norms, uses Cauchy–Schwarz for that finite sum,
and integrates the translated annular majorants from `PunctureCutoff`.
The gradient density is also proved integrable on the whole plane.
-/
public import KsIndexLean.PunctureCutoff

@[expose] public section


noncomputable section

open Real Filter Topology MeasureTheory
open scoped ContDiff

namespace KsIndex.PunctureCutoff

open KsIndex.Surface

variable {k : ℕ}

/-! ### The puncture finset -/

/-- The punctures as a finset: the `2k`-th roots of `−1`. -/
def pF (k : ℕ) : Finset ℂ := Polynomial.nthRootsFinset (2 * k) (-1 : ℂ)

lemma mem_pF (hk : 1 ≤ k) {w : ℂ} : w ∈ pF k ↔ w ∈ punctures k := by
  unfold pF punctures
  rw [Polynomial.mem_nthRootsFinset (by omega)]
  rfl

lemma card_pF_le (k : ℕ) : (pF k).card ≤ 2 * k := by
  unfold pF Polynomial.nthRootsFinset
  exact le_trans (Multiset.toFinset_card_le _) (Polynomial.card_nthRoots _ _)

/-! ### The product cutoff -/

/-- The product cutoff over all punctures. -/
def cutP (k : ℕ) (ε : ℝ) (w : ℂ) : ℝ := ∏ p ∈ pF k, cut1 ε p w

lemma cutP_eq_prod (k : ℕ) (ε : ℝ) : cutP k ε = ∏ p ∈ pF k, cut1 ε p := by
  funext w; rw [Finset.prod_apply]; rfl

lemma cutP_nonneg (k : ℕ) (ε : ℝ) (w : ℂ) : 0 ≤ cutP k ε w :=
  Finset.prod_nonneg fun p _ => cut1_nonneg ε p w

lemma cutP_le_one (k : ℕ) (ε : ℝ) (w : ℂ) : cutP k ε w ≤ 1 :=
  Finset.prod_le_one₀ (fun p _ => cut1_nonneg ε p w) (fun p _ => cut1_le_one ε p w)

lemma cutP_eq_zero (hk : 1 ≤ k) {ε : ℝ} (h0 : 0 < ε) (h1 : ε < 1) {w : ℂ}
    (hw : ∃ p ∈ punctures k, ‖w - p‖ ≤ ε ^ 2) : cutP k ε w = 0 := by
  obtain ⟨p, hp, hwp⟩ := hw
  exact Finset.prod_eq_zero ((mem_pF hk).mpr hp) (cut1_eq_zero h0 h1 hwp)

lemma cutP_eq_one (hk : 1 ≤ k) {ε : ℝ} (h0 : 0 < ε) (h1 : ε < 1) {w : ℂ}
    (hw : ∀ p ∈ punctures k, ε ≤ ‖w - p‖) : cutP k ε w = 1 :=
  Finset.prod_eq_one fun p hp => cut1_eq_one h0 h1 (hw p ((mem_pF hk).mp hp))

lemma cutP_contDiff (k : ℕ) {ε : ℝ} (h0 : 0 < ε) (h1 : ε < 1) : ContDiff ℝ ∞ (cutP k ε) := by
  rw [cutP_eq_prod]
  exact contDiff_prod' fun p _ => cut1_contDiff h0 h1 p

/-! ### Rotation invariance -/

/-- `cut1` depends on `w, p` only through `‖w − p‖`. -/
lemma cut1_congr {ε : ℝ} {p w p' w' : ℂ} (h : ‖w - p‖ = ‖w' - p'‖) :
    cut1 ε p w = cut1 ε p' w' := by
  unfold cut1 arg
  have e : (w = p) ↔ (w' = p') := by
    rw [← sub_eq_zero, ← sub_eq_zero (a := w'), ← norm_eq_zero, ← norm_eq_zero (a := w' - p'), h]
  rw [h]
  by_cases hw : w = p
  · rw [if_pos hw, if_pos (e.mp hw)]
  · rw [if_neg hw, if_neg (fun h' => hw (e.mpr h'))]

/-- Rotations with `a^{2k} = 1` permute the punctures. -/
lemma rot_mem_pF (hk : 1 ≤ k) {a : ℂ} (ha : a ^ (2 * k) = 1) {p : ℂ} (hp : p ∈ pF k) :
    a * p ∈ pF k := by
  rw [mem_pF hk] at hp ⊢
  change (a * p) ^ (2 * k) = -1
  rw [mul_pow, ha, one_mul]; exact hp

/-- **The product cutoff is rotation-invariant** under `a^{2k} = 1`, `‖a‖ = 1`. -/
lemma cutP_rot (hk : 1 ≤ k) (ε : ℝ) {a : ℂ} (ha : ‖a‖ = 1) (hak : a ^ (2 * k) = 1) (w : ℂ) :
    cutP k ε (a * w) = cutP k ε w := by
  have ha0 : a ≠ 0 := by rintro rfl; simp at ha
  have hai : a⁻¹ ^ (2 * k) = 1 := by rw [inv_pow, hak, inv_one]
  unfold cutP
  refine Finset.prod_nbij' (fun p => a⁻¹ * p) (fun p => a * p) (fun p hp => rot_mem_pF hk hai hp)
    (fun p hp => rot_mem_pF hk hak hp) (fun p _ => by field_simp) (fun p _ => by field_simp)
    (fun p _ => cut1_congr ?_)
  rw [show a * w - p = a * (w - a⁻¹ * p) by field_simp, norm_mul, ha, one_mul]

/-! ### The gradient and energy bounds -/

/-- `‖∇cut1‖² ≤ Mψ² L⁻² · annDens ε (w − p)` everywhere. -/
lemma norm_fderiv_cut1_sq_le {ε : ℝ} (h0 : 0 < ε) (h1 : ε < 1) (p w : ℂ) :
    ‖fderiv ℝ (cut1 ε p) w‖ ^ 2 ≤ Mψ ^ 2 * (Lε ε)⁻¹ ^ 2 * annDens ε (w - p) := by
  unfold annDens
  split_ifs with h
  · have hne : w ≠ p := by
      intro hh; subst hh; simp at h; nlinarith [h.1]
    calc ‖fderiv ℝ (cut1 ε p) w‖ ^ 2 ≤ (Mψ * ((Lε ε)⁻¹ * ‖w - p‖⁻¹)) ^ 2 := by
          gcongr; exact norm_fderiv_cut1_le h0 h1 hne
      _ = _ := by ring
  · have hzero : fderiv ℝ (cut1 ε p) w = 0 := by
      push Not at h
      rcases lt_or_ge ‖w - p‖ (ε ^ 2) with hlt | hge
      · have hloc : cut1 ε p =ᶠ[𝓝 w] fun _ => (0 : ℝ) := by
          have hopen : IsOpen {z : ℂ | ‖z - p‖ < ε ^ 2} :=
            isOpen_lt (continuous_id.sub continuous_const).norm continuous_const
          filter_upwards [hopen.mem_nhds hlt] with z hz
          exact cut1_eq_zero h0 h1 (le_of_lt hz)
        rw [hloc.fderiv_eq]; simp
      · have hgt : ε < ‖w - p‖ := h hge
        have hloc : cut1 ε p =ᶠ[𝓝 w] fun _ => (1 : ℝ) := by
          have hopen : IsOpen {z : ℂ | ε < ‖z - p‖} :=
            isOpen_lt continuous_const (continuous_id.sub continuous_const).norm
          filter_upwards [hopen.mem_nhds hgt] with z hz
          exact cut1_eq_one h0 h1 (le_of_lt hz)
        rw [hloc.fderiv_eq]; simp
    rw [hzero]; simp

/-- Derivative of the product cutoff (product rule). -/
lemma hasFDerivAt_cutP (k : ℕ) {ε : ℝ} (h0 : 0 < ε) (h1 : ε < 1) (w : ℂ) :
    HasFDerivAt (cutP k ε)
      (∑ p ∈ pF k, (∏ q ∈ (pF k).erase p, cut1 ε q w) • fderiv ℝ (cut1 ε p) w) w := by
  classical
  have h : ∀ p ∈ pF k, HasFDerivAt (cut1 ε p) (fderiv ℝ (cut1 ε p) w) w := fun p _ =>
    (((cut1_contDiff h0 h1 p).differentiable (by simp)) w).hasFDerivAt
  exact HasFDerivAt.finsetProd h

lemma norm_fderiv_cutP_le (k : ℕ) {ε : ℝ} (h0 : 0 < ε) (h1 : ε < 1) (w : ℂ) :
    ‖fderiv ℝ (cutP k ε) w‖ ≤ ∑ p ∈ pF k, ‖fderiv ℝ (cut1 ε p) w‖ := by
  classical
  rw [(hasFDerivAt_cutP k h0 h1 w).fderiv]
  refine le_trans (norm_sum_le _ _) (Finset.sum_le_sum fun p _ => ?_)
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (Finset.prod_nonneg fun q _ => cut1_nonneg ε q w)]
  exact mul_le_of_le_one_left (norm_nonneg _)
    (Finset.prod_le_one₀ (fun q _ => cut1_nonneg ε q w) (fun q _ => cut1_le_one ε q w))

/-- The complex-valued product cutoff. -/
def cutPC (k : ℕ) (ε : ℝ) (w : ℂ) : ℂ := (cutP k ε w : ℂ)

lemma gradSq_ofReal {f : ℂ → ℝ} {w : ℂ} (hd : DifferentiableAt ℝ f w) :
    gradSq (fun z => (f z : ℂ)) w = ‖fderiv ℝ f w 1‖ ^ 2 + ‖fderiv ℝ f w Complex.I‖ ^ 2 := by
  have hc : (fun z => (f z : ℂ)) = ⇑Complex.ofRealCLM ∘ f := rfl
  unfold gradSq
  rw [hc, (Complex.ofRealCLM.hasFDerivAt.comp w hd.hasFDerivAt).fderiv]
  simp [Complex.norm_real]

/-- **Pointwise energy bound for the product cutoff.** -/
lemma gradSq_cutPC_le (k : ℕ) {ε : ℝ} (h0 : 0 < ε) (h1 : ε < 1) (w : ℂ) :
    gradSq (cutPC k ε) w
      ≤ 2 * (pF k).card * (Mψ ^ 2 * (Lε ε)⁻¹ ^ 2) * ∑ p ∈ pF k, annDens ε (w - p) := by
  have hd : DifferentiableAt ℝ (cutP k ε) w := ((cutP_contDiff k h0 h1).differentiable (by simp)) w
  rw [show cutPC k ε = fun z => (cutP k ε z : ℂ) from rfl, gradSq_ofReal hd]
  calc ‖fderiv ℝ (cutP k ε) w 1‖ ^ 2 + ‖fderiv ℝ (cutP k ε) w Complex.I‖ ^ 2
      ≤ 2 * ‖fderiv ℝ (cutP k ε) w‖ ^ 2 := gradSqR_le w
    _ ≤ 2 * (∑ p ∈ pF k, ‖fderiv ℝ (cut1 ε p) w‖) ^ 2 := by
        gcongr; exact norm_fderiv_cutP_le k h0 h1 w
    _ ≤ 2 * ((pF k).card * ∑ p ∈ pF k, ‖fderiv ℝ (cut1 ε p) w‖ ^ 2) := by
        gcongr; exact sq_sum_le_card_mul_sum_sq
    _ ≤ 2 * ((pF k).card * ∑ p ∈ pF k, Mψ ^ 2 * (Lε ε)⁻¹ ^ 2 * annDens ε (w - p)) := by
        gcongr with p _; exact norm_fderiv_cut1_sq_le h0 h1 p w
    _ = _ := by rw [← Finset.mul_sum]; ring

/-- **The Dirichlet energy of the product cutoff on the disk is `O(1/L)`**:
`∫_D |∇ cutP|² ≤ 4π N² Mψ² / log(1/ε)`, `N = #punctures`. -/
theorem energy_cutP_le (k : ℕ) {ε : ℝ} (h0 : 0 < ε) (h1 : ε < 1) :
    ∫ w in disk, gradSq (cutPC k ε) w ≤ 4 * π * (pF k).card ^ 2 * Mψ ^ 2 / Lε ε := by
  have hL := Lε_pos h0 h1
  set C : ℝ := 2 * (pF k).card * (Mψ ^ 2 * (Lε ε)⁻¹ ^ 2) with hC
  set B : ℂ → ℝ := fun w => C * ∑ p ∈ pF k, annDens ε (w - p) with hB
  have hBint : Integrable B :=
    (integrable_finsetSum _ fun p _ => (annDens_integrable h0 h1).comp_sub_right p).const_mul _
  have hBval : ∫ w, B w = C * ((pF k).card * (2 * π * Lε ε)) := by
    simp only [hB]
    rw [integral_const_mul,
      integral_finsetSum _ fun p _ => (annDens_integrable h0 h1).comp_sub_right p]
    congr 1
    rw [Finset.sum_congr rfl fun p _ => integral_sub_right_eq_self (annDens ε) p,
      Finset.sum_const, nsmul_eq_mul, annDens_integral h0 h1]
    rfl
  have hle : ∀ w, gradSq (cutPC k ε) w ≤ B w := fun w => gradSq_cutPC_le k h0 h1 w
  have hnn : ∀ w, 0 ≤ gradSq (cutPC k ε) w := fun w => by unfold gradSq; positivity
  have hint : Integrable (gradSq (cutPC k ε)) :=
    hBint.mono' (measurable_gradSq _).aestronglyMeasurable
      (Eventually.of_forall fun w => by rw [Real.norm_eq_abs, abs_of_nonneg (hnn w)]; exact hle w)
  calc ∫ w in disk, gradSq (cutPC k ε) w
      ≤ ∫ w, gradSq (cutPC k ε) w := setIntegral_le_integral hint (Eventually.of_forall hnn)
    _ ≤ ∫ w, B w := integral_mono hint hBint hle
    _ = C * ((pF k).card * (2 * π * Lε ε)) := hBval
    _ = 4 * π * (pF k).card ^ 2 * Mψ ^ 2 / Lε ε := by rw [hC]; field_simp; ring

/-- Integrability of the cutoff's gradient density on `ℂ` (hence on the disk). -/
lemma integrable_gradSq_cutPC (k : ℕ) {ε : ℝ} (h0 : 0 < ε) (h1 : ε < 1) :
    Integrable (gradSq (cutPC k ε)) := by
  set C : ℝ := 2 * (pF k).card * (Mψ ^ 2 * (Lε ε)⁻¹ ^ 2) with hC
  set B : ℂ → ℝ := fun w => C * ∑ p ∈ pF k, annDens ε (w - p) with hB
  have hBint : Integrable B :=
    (integrable_finsetSum _ fun p _ => (annDens_integrable h0 h1).comp_sub_right p).const_mul _
  have hnn : ∀ w, 0 ≤ gradSq (cutPC k ε) w := fun w => by unfold gradSq; positivity
  exact hBint.mono' (measurable_gradSq _).aestronglyMeasurable
    (Eventually.of_forall fun w => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hnn w)]; exact gradSq_cutPC_le k h0 h1 w)

end KsIndex.PunctureCutoff
