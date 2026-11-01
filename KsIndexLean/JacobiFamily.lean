module

/-
# Three independent translation Jacobi fields

For `k ≥ 2`, the functions `nu1`, `nu2` and `nu3` are smooth on the
complex plane and solve the geometric Jacobi equation on the disk.
Their squared norms sum to one, so each is bounded by one. Under the
seam reflection `σ w = 1 / conj w` away from zero, `nu1` and `nu2` are
even and `nu3` is odd.

This file assembles these functions into `BoundedJacobi k m` families.
`symFam` restricts each function to the closed disk on every copy and
multiplies it by the appropriate parity sign. Reflection parity gives
smooth gluing across the seams. Seam values agree directly for the even
fields; the odd field vanishes on the unit circle. The representative is
then set to zero at the deleted punctures by `punc0`, preserving the
smoothness, boundedness, Jacobi equation and seam-value conditions.

Evaluation on copy zero at `1`, `exp (iπ / (2(k−1)))` and `0` gives a
diagonal matrix with entries `1`, `1`, `-1`. These points avoid the
punctures, so normalization does not change the evaluations. The resulting
linear independence proves `three_le_nulSurface : 3 ≤ nulSurface k m`
for every natural `m` in the disk-chain encoding and every `k ≥ 2`.
-/
public import Mathlib
public import KsIndexLean.JacobiFieldsSym
public import KsIndexLean.SurfaceForm

@[expose] public section


open Complex Filter Topology
open scoped ContDiff

noncomputable section

namespace KsIndex.JacobiFamily

open KsIndex.Surface KsIndex.JacobiFields KsIndex.SurfaceForm

/-! ### The symmetric family -/

/-- Cut-off of a function on `ℂ` to the closed unit disk. -/
def cutD (f : ℂ → ℂ) (w : ℂ) : ℂ := if ‖w‖ ≤ 1 then f w else 0

/-- `ε^{parity n} · f` on the closed disk of copy `n`, `0` outside. -/
def symFam (m : ℕ) (ε : ℂ) (f : ℂ → ℂ) : ZMod (2 * m) → ℂ → ℂ :=
  fun n w => ε ^ (parity m n).val * cutD f w

lemma cutD_of_le {f : ℂ → ℂ} {w : ℂ} (hw : ‖w‖ ≤ 1) : cutD f w = f w := if_pos hw

lemma cutD_of_lt {f : ℂ → ℂ} {w : ℂ} (hw : 1 < ‖w‖) : cutD f w = 0 := if_neg (not_le.mpr hw)

lemma symFam_of_le {m : ℕ} {ε : ℂ} {f : ℂ → ℂ} (n : ZMod (2 * m)) {w : ℂ} (hw : ‖w‖ ≤ 1) :
    symFam m ε f n w = ε ^ (parity m n).val * f w := by
  simp [symFam, cutD_of_le hw]

lemma symFam_zero_copy {m : ℕ} {ε : ℂ} {f : ℂ → ℂ} {w : ℂ} (hw : ‖w‖ ≤ 1) :
    symFam m ε f 0 w = f w := by
  simp [symFam_of_le (m := m) (ε := ε) (f := f) 0 hw]

lemma parity_val_lt_two (m : ℕ) (n : ZMod (2 * m)) : (parity m n).val < 2 := ZMod.val_lt _

/-- `ε^{1−v} · ε = ε^v` for `ε = ±1` and `v ∈ {0,1}`. -/
lemma pow_sub_mul {ε : ℂ} (hε : ε = 1 ∨ ε = -1) {v : ℕ} (hv : v < 2) :
    ε ^ (1 - v) * ε = ε ^ v := by
  interval_cases v <;> rcases hε with rfl | rfl <;> norm_num

lemma norm_sigma {w : ℂ} : ‖(1 : ℂ) / (starRingEnd ℂ) w‖ = 1 / ‖w‖ := by
  rw [norm_div, norm_one, Complex.norm_conj]

/-- **Glue formula.**  For `f ∘ σ = ε f` (`ε = ±1`) the glued function across seam `(n, n+1)` is
`ε^{parity n} · f` everywhere. -/
lemma glue_symFam {m : ℕ} {ε : ℂ} (hε : ε = 1 ∨ ε = -1) {f : ℂ → ℂ}
    (hf : ∀ w : ℂ, w ≠ 0 → f (1 / (starRingEnd ℂ) w) = ε * f w) (n : ZMod (2 * m)) :
    glue (symFam m ε f) n = fun w => ε ^ (parity m n).val * f w := by
  funext w
  unfold glue
  split_ifs with hw
  · exact symFam_of_le n hw
  · push Not at hw
    have hw0 : w ≠ 0 := by
      intro h; subst h; simp at hw; linarith
    have hσ : ‖(1 : ℂ) / (starRingEnd ℂ) w‖ ≤ 1 := by
      rw [norm_sigma]
      exact (div_le_one (by positivity)).mpr hw.le
    rw [symFam_of_le _ hσ, hf w hw0, parity_succ_val, ← mul_assoc,
      pow_sub_mul hε (parity_val_lt_two m n)]

/-! ### Membership in `BoundedJacobi` -/

lemma isSmooth_symFam {k m : ℕ} {ε : ℂ} (hε : ε = 1 ∨ ε = -1) {f : ℂ → ℂ}
    (hsm : ContDiff ℝ ∞ f)
    (hf : ∀ w : ℂ, w ≠ 0 → f (1 / (starRingEnd ℂ) w) = ε * f w) :
    IsSmooth k m (symFam m ε f) := by
  refine ⟨fun n => ?_, fun n w _ => ?_, fun n w hw => ?_⟩
  · refine ((contDiff_const (c := ε ^ (parity m n).val)).mul hsm).contDiffOn.congr
      fun w hw => ?_
    have : ‖w‖ ≤ 1 := by
      have := Metric.mem_ball.mp hw; rw [dist_zero_right] at this; exact this.le
    exact symFam_of_le n this
  · rw [glue_symFam hε hf n]
    exact (contDiff_const.mul hsm).contDiffAt
  · simp [symFam, cutD_of_lt hw]

lemma isBounded_symFam {m : ℕ} {ε : ℂ} (hε : ε = 1 ∨ ε = -1) {f : ℂ → ℂ}
    (hb : ∀ w, ‖f w‖ ≤ 1) : IsBounded (symFam m ε f) := by
  refine ⟨1, fun n w => ?_⟩
  have hε1 : ‖ε‖ = 1 := by rcases hε with rfl | rfl <;> simp
  unfold symFam cutD
  rw [norm_mul, norm_pow, hε1, one_pow, one_mul]
  split_ifs
  · exact hb w
  · simp

/-- The flat Laplacian only depends on the germ. -/
lemma laplacian_congr {f g : ℂ → ℂ} {w : ℂ} (h : f =ᶠ[𝓝 w] g) :
    laplacian f w = laplacian g w := by
  have hh : ∀ᶠ z in 𝓝 w, f =ᶠ[𝓝 z] g := eventually_eventually_nhds.mpr h
  have h1 : (fun z => fderiv ℝ f z 1) =ᶠ[𝓝 w] fun z => fderiv ℝ g z 1 := by
    filter_upwards [hh] with z hz using by rw [hz.fderiv_eq]
  have h2 : (fun z => fderiv ℝ f z I) =ᶠ[𝓝 w] fun z => fderiv ℝ g z I := by
    filter_upwards [hh] with z hz using by rw [hz.fderiv_eq]
  simp only [laplacian, h1.fderiv_eq, h2.fderiv_eq]

lemma isJacobiField_symFam {k m : ℕ} {ε : ℂ} {f : ℂ → ℂ}
    (hsm : ContDiff ℝ ∞ f)
    (hJ : ∀ w ∈ disk, laplacianG k f w + ((absA k w ^ 2 : ℝ) : ℂ) * f w = 0) :
    IsJacobiField k m (symFam m ε f) := by
  intro n w hw
  set c : ℂ := ε ^ (parity m n).val
  have hloc : symFam m ε f n =ᶠ[𝓝 w] c • f := by
    filter_upwards [Metric.isOpen_ball.mem_nhds hw] with z hz
    have : ‖z‖ ≤ 1 := by
      have := Metric.mem_ball.mp hz; rw [dist_zero_right] at this; exact this.le
    simp [symFam_of_le n this, c]
  have hval : symFam m ε f n w = c * f w := by
    have : ‖w‖ ≤ 1 := by
      have := Metric.mem_ball.mp hw; rw [dist_zero_right] at this; exact this.le
    exact symFam_of_le n this
  rw [laplacianG, laplacian_congr hloc, laplacian_smul c hsm.contDiffAt, hval]
  have := hJ w hw
  rw [laplacianG] at this
  linear_combination c * this

/-- The odd/even parity hypothesis in the form used above, from the `σ`-lemmas. -/
lemma nu1_refl (k : ℕ) (hk : 2 ≤ k) : ∀ w : ℂ, w ≠ 0 →
    nu1 k (1 / (starRingEnd ℂ) w) = 1 * nu1 k w := fun w hw => by
  rw [one_mul]; exact nu1_sigma k hk hw

lemma nu2_refl (k : ℕ) (hk : 2 ≤ k) : ∀ w : ℂ, w ≠ 0 →
    nu2 k (1 / (starRingEnd ℂ) w) = 1 * nu2 k w := fun w hw => by
  rw [one_mul]; exact nu2_sigma k hk hw

lemma nu3_refl (k : ℕ) (hk : 2 ≤ k) : ∀ w : ℂ, w ≠ 0 →
    nu3 k (1 / (starRingEnd ℂ) w) = -1 * nu3 k w := fun w hw => by
  rw [neg_one_mul]; exact nu3_sigma k hk hw

lemma nu1_norm_le (k : ℕ) (hk : 2 ≤ k) (w : ℂ) : ‖nu1 k w‖ ≤ 1 := by
  have h := nu_normSq k hk w
  nlinarith [norm_nonneg (nu1 k w), sq_nonneg ‖nu2 k w‖, sq_nonneg ‖nu3 k w‖]

lemma nu2_norm_le (k : ℕ) (hk : 2 ≤ k) (w : ℂ) : ‖nu2 k w‖ ≤ 1 := by
  have h := nu_normSq k hk w
  nlinarith [norm_nonneg (nu2 k w), sq_nonneg ‖nu1 k w‖, sq_nonneg ‖nu3 k w‖]

lemma nu3_norm_le (k : ℕ) (hk : 2 ≤ k) (w : ℂ) : ‖nu3 k w‖ ≤ 1 := by
  have h := nu_normSq k hk w
  nlinarith [norm_nonneg (nu3 k w), sq_nonneg ‖nu1 k w‖, sq_nonneg ‖nu2 k w‖]

/-! ### Puncture normalization

The ambient total-function encoding carries a value at each deleted puncture that is not part of
the surface; `BoundedJacobi` requires that value to be `0` (`PunctureZero`).  The translation
fields need not vanish at the punctures, so each representative is normalized by
zeroing it there (`punc0`). Smoothness and the Jacobi equation are checked on
the open disks and seam arcs, while the exterior-zero condition is checked
outside the closed disk. These sets contain no punctures, and the relevant
local equalities follow from closedness of the puncture set. Boundedness is
preserved because the replacement value is zero. -/

/-- All punctures lie on the unit circle. -/
lemma punctures_norm_eq_one {k : ℕ} (hk : 1 ≤ k) {p : ℂ} (hp : p ∈ punctures k) : ‖p‖ = 1 := by
  simp only [punctures, Set.mem_setOf_eq] at hp
  have h1 : ‖p‖ ^ (2 * k) = 1 := by rw [← norm_pow, hp, norm_neg, norm_one]
  rcases lt_trichotomy ‖p‖ 1 with h | h | h
  · exact absurd h1 (ne_of_lt (pow_lt_one₀ (norm_nonneg p) h (by omega)))
  · exact h
  · exact absurd h1 (ne_of_gt (one_lt_pow₀ h (by omega)))

/-- The puncture set is closed. -/
lemma isClosed_punctures (k : ℕ) : IsClosed (punctures k) := by
  have h : punctures k = (fun w : ℂ => w ^ (2 * k)) ⁻¹' {-1} := by ext w; simp [punctures]
  rw [h]; exact isClosed_singleton.preimage (continuous_pow (2 * k))

/-- `z² = −1` forces `Re z = 0`. -/
lemma sq_eq_neg_one_re_zero {z : ℂ} (h : z ^ 2 = -1) : z.re = 0 := by
  have hfac : (z - I) * (z + I) = 0 := by
    rw [show (z - I) * (z + I) = z ^ 2 - I ^ 2 from by ring, Complex.I_sq, h]; ring
  rcases mul_eq_zero.mp hfac with h1 | h1
  · rw [sub_eq_zero.mp h1, Complex.I_re]
  · rw [add_eq_zero_iff_eq_neg.mp h1, Complex.neg_re, Complex.I_re, neg_zero]

/-- `Re(pᵏ) = 0` at every puncture. -/
lemma punctures_re_pow_eq_zero {k : ℕ} {p : ℂ} (hp : p ∈ punctures k) : (p ^ k).re = 0 := by
  apply sq_eq_neg_one_re_zero
  simp only [punctures, Set.mem_setOf_eq] at hp
  rw [← pow_mul, mul_comm]; exact hp

/-- Seam-arc points are not punctures (the arcs exclude the junctions `Re(wᵏ) = 0`). -/
lemma arc_notMem_punctures {k n : ℕ} {w : ℂ} (hw : w ∈ arc k n) : w ∉ punctures k := by
  intro hp
  simp only [arc, Set.mem_setOf_eq] at hw
  rw [punctures_re_pow_eq_zero hp, mul_zero] at hw
  exact lt_irrefl 0 hw.2

/-- Points outside the closed disk are not punctures. -/
lemma notMem_punctures_of_one_lt {k : ℕ} (hk : 1 ≤ k) {w : ℂ} (hw : 1 < ‖w‖) : w ∉ punctures k :=
  fun hp => by have := punctures_norm_eq_one hk hp; linarith

/-- Zero out the deleted punctures — a representative normalization. -/
def punc0 (k : ℕ) {m : ℕ} (u : ZMod (2 * m) → ℂ → ℂ) : ZMod (2 * m) → ℂ → ℂ :=
  fun n => Set.indicator (punctures k)ᶜ (u n)

lemma punc0_of_notMem (k : ℕ) {m : ℕ} (u : ZMod (2 * m) → ℂ → ℂ) (n : ZMod (2 * m)) {w : ℂ}
    (hw : w ∉ punctures k) : punc0 k u n w = u n w :=
  Set.indicator_of_mem hw (u n)

lemma punc0_of_mem (k : ℕ) {m : ℕ} (u : ZMod (2 * m) → ℂ → ℂ) (n : ZMod (2 * m)) {w : ℂ}
    (hw : w ∈ punctures k) : punc0 k u n w = 0 :=
  Set.indicator_of_notMem (not_not_intro hw) (u n)

lemma punctureZero_punc0 (k : ℕ) {m : ℕ} (u : ZMod (2 * m) → ℂ → ℂ) :
    PunctureZero k (punc0 k u) := fun n p hp => punc0_of_mem k u n hp

lemma isBounded_punc0 {k m : ℕ} {u : ZMod (2 * m) → ℂ → ℂ} (hu : IsBounded u) :
    IsBounded (punc0 k u) := by
  obtain ⟨C, hC⟩ := hu
  refine ⟨C, fun n w => ?_⟩
  by_cases hw : w ∈ punctures k
  · rw [punc0_of_mem k u n hw, norm_zero]; exact le_trans (norm_nonneg (u n w)) (hC n w)
  · rw [punc0_of_notMem k u n hw]; exact hC n w

lemma isSmooth_punc0 {k m : ℕ} (hk : 1 ≤ k) {u : ZMod (2 * m) → ℂ → ℂ} (hu : IsSmooth k m u) :
    IsSmooth k m (punc0 k u) := by
  refine ⟨fun n => (hu.1 n).congr
      (fun z hz => punc0_of_notMem k u n (punctures_notMem_disk hk hz)),
    fun n w hw => ?_, fun n w hw => ?_⟩
  · have hnotp : w ∉ punctures k := arc_notMem_punctures hw
    have heq : glue (punc0 k u) n =ᶠ[𝓝 w] glue u n := by
      filter_upwards [(isClosed_punctures k).isOpen_compl.mem_nhds hnotp] with z hz
      unfold glue
      split_ifs with hzle
      · exact punc0_of_notMem k u n hz
      · push_neg at hzle
        refine punc0_of_notMem k u (n + 1) (punctures_notMem_disk hk ?_)
        rw [disk, Metric.mem_ball, dist_zero_right, norm_sigma]
        exact (div_lt_one (by linarith)).mpr hzle
    exact (hu.2.1 n w hw).congr_of_eventuallyEq heq
  · rw [punc0_of_notMem k u n (notMem_punctures_of_one_lt hk hw)]; exact hu.2.2 n w hw

lemma isJacobiField_punc0 {k m : ℕ} (hk : 1 ≤ k) {u : ZMod (2 * m) → ℂ → ℂ}
    (hJ : IsJacobiField k m u) : IsJacobiField k m (punc0 k u) := by
  intro n w hw
  have hnotp : w ∉ punctures k := punctures_notMem_disk hk hw
  have hloc : punc0 k u n =ᶠ[𝓝 w] u n := by
    filter_upwards [(isClosed_punctures k).isOpen_compl.mem_nhds hnotp] with z hz
    exact punc0_of_notMem k u n hz
  have hval : punc0 k u n w = u n w := punc0_of_notMem k u n hnotp
  simp only [laplacianG, laplacian_congr hloc]
  rw [hval]
  simpa only [laplacianG] using hJ n w hw

/-! ### Seam single-valuedness of the symmetric family -/

/-- `σ = 1/w̄` fixes the unit circle pointwise. -/
lemma sigma_fix {w : ℂ} (hw : ‖w‖ = 1) : (1 : ℂ) / (starRingEnd ℂ) w = w := by
  have hw0 : w ≠ 0 := by rintro rfl; simp at hw
  rw [one_div]
  refine inv_eq_of_mul_eq_one_right ?_
  rw [Complex.conj_mul', hw]; norm_num

/-- **`ν₃` vanishes on the unit circle**: `nu3_refl` gives `ν₃(σw) = −ν₃(w)`, and `σ` fixes the
circle (`sigma_fix`), so `ν₃(w) = −ν₃(w)`, whence `ν₃(w) = 0`. -/
lemma nu3_zero_on_circle (k : ℕ) (hk : 2 ≤ k) {w : ℂ} (hw : ‖w‖ = 1) : nu3 k w = 0 := by
  have hw0 : w ≠ 0 := by rintro rfl; simp at hw
  have hrefl := nu3_refl k hk w hw0
  rw [sigma_fix hw] at hrefl
  linear_combination (1 / 2 : ℂ) * hrefl

/-- **Seam single-valuedness of `symFam`.**  On a seam arc `‖w‖ = 1`, so `cutD f w = f w`; the two
copies carry `ε^{parity(n+1)}` and `ε^{parity n}`, which agree trivially for `ε = 1` and (for
`ε = −1`) because `f` vanishes on the circle (hypothesis `hf`). -/
lemma seamVal_symFam {k m : ℕ} {ε : ℂ} (hε : ε = 1 ∨ ε = -1) {f : ℂ → ℂ}
    (hf : ε = -1 → ∀ w : ℂ, ‖w‖ = 1 → f w = 0) : SeamVal k (symFam m ε f) := by
  intro n w hw
  simp only [seamArc, arc, Set.mem_setOf_eq] at hw
  have hle : ‖w‖ ≤ 1 := le_of_eq hw.1
  rw [symFam_of_le (n + 1) hle, symFam_of_le n hle]
  rcases hε with rfl | rfl
  · simp
  · rw [hf rfl w hw.1]; ring

/-- Seam single-valuedness is preserved by `punc0` (seam points are not punctures). -/
lemma seamVal_punc0 {k m : ℕ} {u : ZMod (2 * m) → ℂ → ℂ} (hu : SeamVal k u) :
    SeamVal k (punc0 k u) := by
  intro n w hw
  have hnotp : w ∉ punctures k := arc_notMem_punctures hw
  rw [punc0_of_notMem k u (n + 1) hnotp, punc0_of_notMem k u n hnotp]
  exact hu n w hw

/-- The translation Jacobi field for `e_1`, as an element of `BoundedJacobi k m`. -/
def J1 (k m : ℕ) (hk : 2 ≤ k) : BoundedJacobi k m :=
  ⟨punc0 k (symFam m 1 (nu1 k)),
    isSmooth_punc0 (by omega) (isSmooth_symFam (Or.inl rfl) (nu1_contDiff k hk) (nu1_refl k hk)),
    isBounded_punc0 (isBounded_symFam (Or.inl rfl) (nu1_norm_le k hk)),
    isJacobiField_punc0 (by omega)
      (isJacobiField_symFam (nu1_contDiff k hk) fun _ hw => laplacianG_nu1 hk hw),
    punctureZero_punc0 k _,
    seamVal_punc0 (seamVal_symFam (Or.inl rfl) (fun h => absurd h (by norm_num)))⟩

def J2 (k m : ℕ) (hk : 2 ≤ k) : BoundedJacobi k m :=
  ⟨punc0 k (symFam m 1 (nu2 k)),
    isSmooth_punc0 (by omega) (isSmooth_symFam (Or.inl rfl) (nu2_contDiff k hk) (nu2_refl k hk)),
    isBounded_punc0 (isBounded_symFam (Or.inl rfl) (nu2_norm_le k hk)),
    isJacobiField_punc0 (by omega)
      (isJacobiField_symFam (nu2_contDiff k hk) fun _ hw => laplacianG_nu2 hk hw),
    punctureZero_punc0 k _,
    seamVal_punc0 (seamVal_symFam (Or.inl rfl) (fun h => absurd h (by norm_num)))⟩

def J3 (k m : ℕ) (hk : 2 ≤ k) : BoundedJacobi k m :=
  ⟨punc0 k (symFam m (-1) (nu3 k)),
    isSmooth_punc0 (by omega) (isSmooth_symFam (Or.inr rfl) (nu3_contDiff k hk) (nu3_refl k hk)),
    isBounded_punc0 (isBounded_symFam (Or.inr rfl) (nu3_norm_le k hk)),
    isJacobiField_punc0 (by omega)
      (isJacobiField_symFam (nu3_contDiff k hk) fun _ hw => laplacianG_nu3 hk hw),
    punctureZero_punc0 k _,
    seamVal_punc0 (seamVal_symFam (Or.inr rfl) (fun _ w hw => nu3_zero_on_circle k hk hw))⟩

/-- The three translation Jacobi fields, indexed by `Fin 3`. -/
def transJ (k m : ℕ) (hk : 2 ≤ k) : Fin 3 → BoundedJacobi k m :=
  ![J1 k m hk, J2 k m hk, J3 k m hk]

/-! ### Linear independence by evaluation -/

/-- The test point `e^{iπ/(2(k−1))}`, at which `w^{k−1} = i`. -/
def wI (k : ℕ) : ℂ := exp (((Real.pi / (2 * (k - 1 : ℝ))) : ℝ) * I)

lemma norm_wI (k : ℕ) : ‖wI k‖ = 1 := Complex.norm_exp_ofReal_mul_I _

lemma wI_pow (k : ℕ) (hk : 2 ≤ k) : wI k ^ (k - 1) = I := by
  unfold wI
  rw [← Complex.exp_nat_mul]
  have hk' : ((k - 1 : ℕ) : ℂ) = ((k : ℝ) - 1 : ℝ) := by
    rw [Nat.cast_sub (by omega)]; push_cast; ring
  have hne : ((k : ℝ) - 1 : ℝ) ≠ 0 := by
    have : (2 : ℝ) ≤ k := by exact_mod_cast hk
    linarith
  have : ((k - 1 : ℕ) : ℂ) * (((Real.pi / (2 * (k - 1 : ℝ))) : ℝ) * I)
      = ((Real.pi / 2 : ℝ) : ℂ) * I := by
    rw [hk']
    have hne' : ((k : ℂ) - 1) ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast (show k ≠ 1 by omega))
    push_cast
    field_simp
  rw [this]
  apply Complex.ext
  · rw [Complex.exp_ofReal_mul_I_re, Real.cos_pi_div_two, Complex.I_re]
  · rw [Complex.exp_ofReal_mul_I_im, Real.sin_pi_div_two, Complex.I_im]

/-- The evaluation points on copy `0`. -/
def pts (k : ℕ) : Fin 3 → ℂ := ![1, wI k, 0]

lemma norm_pts_le (k : ℕ) (j : Fin 3) : ‖pts k j‖ ≤ 1 := by
  fin_cases j <;> simp [pts, norm_wI]

/-- Evaluation of the copy-`0` function at the three test points. -/
def ev (k m : ℕ) : BoundedJacobi k m →ₗ[ℂ] (Fin 3 → ℂ) where
  toFun u j := (u : ZMod (2 * m) → ℂ → ℂ) 0 (pts k j)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

lemma nu1_one (k : ℕ) : nu1 k 1 = 1 := by
  simp [nu1]; norm_num
lemma nu2_one (k : ℕ) : nu2 k 1 = 0 := by simp [nu2]
lemma nu3_one (k : ℕ) : nu3 k 1 = 0 := by simp [nu3]

lemma nu1_wI (k : ℕ) (hk : 2 ≤ k) : nu1 k (wI k) = 0 := by
  simp [nu1, wI_pow k hk, norm_wI]
lemma nu2_wI (k : ℕ) (hk : 2 ≤ k) : nu2 k (wI k) = 1 := by
  simp [nu2, wI_pow k hk, norm_wI]; norm_num
lemma nu3_wI (k : ℕ) : nu3 k (wI k) = 0 := by simp [nu3, norm_wI]

lemma nu1_zero (k : ℕ) (hk : 2 ≤ k) : nu1 k 0 = 0 := by
  simp [nu1, zero_pow (show k - 1 ≠ 0 by omega)]
lemma nu2_zero (k : ℕ) (hk : 2 ≤ k) : nu2 k 0 = 0 := by
  simp [nu2, zero_pow (show k - 1 ≠ 0 by omega)]
lemma nu3_zero (k : ℕ) (hk : 2 ≤ k) : nu3 k 0 = -1 := by
  simp [nu3, zero_pow (show 2 * k - 2 ≠ 0 by omega)]

/-- The diagonal entries. -/
def dg : Fin 3 → ℂˣ := ![1, 1, -1]

/-! ### The evaluation points avoid the punctures -/

lemma one_notMem_punctures (k : ℕ) : (1 : ℂ) ∉ punctures k := by
  intro h; simp only [punctures, Set.mem_setOf_eq, one_pow] at h
  exact (by norm_num : (1 : ℂ) ≠ -1) h

lemma zero_notMem_punctures {k : ℕ} (hk : 1 ≤ k) : (0 : ℂ) ∉ punctures k := by
  intro h; simp only [punctures, Set.mem_setOf_eq, zero_pow (show 2 * k ≠ 0 by omega)] at h
  exact (by norm_num : (0 : ℂ) ≠ -1) h

lemma wI_notMem_punctures (k : ℕ) (hk : 2 ≤ k) : wI k ∉ punctures k := by
  simp only [punctures, Set.mem_setOf_eq]
  intro h
  have hkm1 : wI k ^ (2 * (k - 1)) = -1 := by
    rw [show 2 * (k - 1) = (k - 1) * 2 from by ring, pow_mul, wI_pow k hk, Complex.I_sq]
  have hsq : wI k ^ 2 = 1 := by
    have e : wI k ^ (2 * k) = wI k ^ (2 * (k - 1)) * wI k ^ 2 := by
      rw [← pow_add]; congr 1; omega
    rw [e, hkm1] at h; linear_combination -h
  have hcontra : wI k ^ (2 * (k - 1)) = 1 := by rw [pow_mul, hsq, one_pow]
  rw [hkm1] at hcontra
  exact absurd hcontra (by norm_num)

lemma pts_notMem_punctures (k : ℕ) (hk : 2 ≤ k) (j : Fin 3) : pts k j ∉ punctures k := by
  fin_cases j
  · exact one_notMem_punctures k
  · exact wI_notMem_punctures k hk
  · exact zero_notMem_punctures (by omega)

lemma ev_transJ (k m : ℕ) (hk : 2 ≤ k) :
    ev k m ∘ transJ k m hk = fun i => (dg i : ℂ) • Pi.basisFun ℂ (Fin 3) i := by
  funext i j
  have hj : pts k j ∉ punctures k := pts_notMem_punctures k hk j
  have key : (transJ k m hk i : ZMod (2 * m) → ℂ → ℂ) 0 (pts k j)
      = ![symFam m 1 (nu1 k), symFam m 1 (nu2 k), symFam m (-1) (nu3 k)] i 0 (pts k j) := by
    fin_cases i <;> exact punc0_of_notMem k _ 0 hj
  simp only [Function.comp, ev, LinearMap.coe_mk, AddHom.coe_mk, key, Pi.smul_apply,
    Pi.basisFun_apply, Pi.single_apply, smul_eq_mul]
  fin_cases i <;> fin_cases j <;>
    simp [dg, pts, symFam, cutD, norm_wI, nu1_one k, nu2_one, nu3_one,
      nu1_wI k hk, nu2_wI k hk, nu3_wI, nu1_zero k hk, nu2_zero k hk, nu3_zero k hk]

theorem linearIndependent_transJ (k m : ℕ) (hk : 2 ≤ k) :
    LinearIndependent ℂ (transJ k m hk) := by
  apply LinearIndependent.of_comp (ev k m)
  rw [ev_transJ k m hk]
  exact (Pi.basisFun ℂ (Fin 3)).linearIndependent.units_smul dg

/-- **`nul(Ξ_{k,m}) ≥ 3`** for every `k ≥ 2` and every `m`: the three translation Jacobi fields. -/
theorem three_le_nulSurface (k m : ℕ) (hk : 2 ≤ k) : 3 ≤ nulSurface k m := by
  have h := (linearIndependent_transJ k m hk).cardinal_le_rank
  rw [Cardinal.mk_fin] at h
  have h' : Cardinal.toENat ((3 : ℕ) : Cardinal)
      ≤ Cardinal.toENat (Module.rank ℂ (BoundedJacobi k m)) := Cardinal.toENat.monotone' h
  rw [Cardinal.toENat_nat] at h'
  unfold nulSurface
  exact_mod_cast h'

end KsIndex.JacobiFamily

end
