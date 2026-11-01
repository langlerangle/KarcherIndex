module

/-
# A smooth cutoff near the closed slit and a mixed test function

`cutSlit k δ c = 1 - aRad δ * bAng k c` uses two smooth transition profiles.
It is globally smooth and takes values in `[0, 1]`. For positive `δ` and `c`,
it vanishes where `‖w‖² ≥ 1-δ` and `Re(w^k) ≤ c`, and equals one where
`‖w‖² ≤ 1-2δ` or `Re(w^k) ≥ 2c`. For `k ≥ 1`, the vanishing region contains
a uniform metric neighborhood of the closed slit
`{w | ‖w‖ = 1 ∧ Re(w^k) ≤ 0}`. The proof uses the local Lipschitz bound
for `Re(w^k)` near the unit circle.

`groundR` is globally smooth and, for `k ≥ 1`, equals the radial profile
`gRad k 0 ‖w‖`. Multiplying it by the cutoff and setting the result to zero
outside the closed disk defines `zModeCut`. For `k ≥ 1` and positive cutoff
parameters, `zModeCut_mem` places this function in
`NatCc k true false ⊓ Erot1 k 0`. The slit neighborhood also contains the
punctures, supplying the required vanishing near them. Rotation invariance
places the function in the trivial character class.

This module establishes the test function's domain membership; estimates
for its quadratic-form value are separate.
-/
public import KsIndexLean.SeamLowerNat
public import KsIndexLean.PunctureCutoff
public import KsIndexLean.RadialGround

@[expose] public section


noncomputable section

open Complex Real Set Filter Topology
open KsIndex.Surface KsIndex.SurfaceForm KsIndex.SingleDiskBridge KsIndex.SurfaceSym
  KsIndex.Radial KsIndex.Bracket
open scoped ContDiff

namespace KsIndex.SingleDisk

variable {k : ℕ}

/-! ### The Lipschitz bound for `Re(w^k)` near the unit circle -/

/-- `|Re(w^k) − Re(p^k)| ≤ k·2^{k−1}·‖w − p‖` for `‖p‖ = 1`, `‖w − p‖ ≤ 1`. -/
lemma re_pow_lip {w p : ℂ} (hp : ‖p‖ = 1) (hwp : ‖w - p‖ ≤ 1) :
    |(w ^ k).re - (p ^ k).re| ≤ (k : ℝ) * 2 ^ (k - 1) * ‖w - p‖ := by
  have hw2 : ‖w‖ ≤ 2 := by
    have h := norm_add_le (w - p) p
    rw [sub_add_cancel, hp] at h
    linarith
  have hterm : ∀ i ∈ Finset.range k, ‖w ^ i * p ^ (k - 1 - i)‖ ≤ (2 : ℝ) ^ (k - 1) := by
    intro i hi
    rw [norm_mul, norm_pow, norm_pow, hp, one_pow, mul_one]
    calc ‖w‖ ^ i ≤ 2 ^ i := pow_le_pow_left₀ (norm_nonneg w) hw2 i
      _ ≤ 2 ^ (k - 1) :=
          pow_le_pow_right₀ one_le_two (by have := Finset.mem_range.mp hi; omega)
  have hsum : ‖∑ i ∈ Finset.range k, w ^ i * p ^ (k - 1 - i)‖ ≤ (k : ℝ) * 2 ^ (k - 1) := by
    calc ‖∑ i ∈ Finset.range k, w ^ i * p ^ (k - 1 - i)‖
        ≤ ∑ i ∈ Finset.range k, ‖w ^ i * p ^ (k - 1 - i)‖ := norm_sum_le _ _
      _ ≤ ∑ _i ∈ Finset.range k, (2 : ℝ) ^ (k - 1) := Finset.sum_le_sum hterm
      _ = (k : ℝ) * 2 ^ (k - 1) := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  calc |(w ^ k).re - (p ^ k).re| = |(w ^ k - p ^ k).re| := by rw [Complex.sub_re]
    _ ≤ ‖w ^ k - p ^ k‖ := Complex.abs_re_le_norm _
    _ = ‖(∑ i ∈ Finset.range k, w ^ i * p ^ (k - 1 - i)) * (w - p)‖ := by
        rw [(Commute.all w p).geom_sum₂_mul]
    _ = ‖∑ i ∈ Finset.range k, w ^ i * p ^ (k - 1 - i)‖ * ‖w - p‖ := norm_mul _ _
    _ ≤ (k : ℝ) * 2 ^ (k - 1) * ‖w - p‖ := mul_le_mul_of_nonneg_right hsum (norm_nonneg _)

/-- **A uniform metric neighbourhood of the closed slit** lies inside the region
`{‖w‖² ≥ 1−δ, Re(w^k) ≤ c}` where the cut-off vanishes. -/
lemma slit_nbhd (hk : 1 ≤ k) {δ c : ℝ} (hδ : 0 < δ) (hc : 0 < c) :
    ∃ ε > 0, ∀ w : ℂ, (∃ p ∈ slit k, ‖w - p‖ < ε) →
      1 - δ ≤ w.re ^ 2 + w.im ^ 2 ∧ (w ^ k).re ≤ c := by
  set L : ℝ := (k : ℝ) * 2 ^ (k - 1) with hLdef
  have hL : 0 < L := by
    have hk' : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
    positivity
  refine ⟨min (min (δ / 2) 1) (c / L),
    lt_min (lt_min (by positivity) one_pos) (by positivity), ?_⟩
  rintro w ⟨p, ⟨hpn, hpre⟩, hwp⟩
  have hε1 : ‖w - p‖ ≤ 1 := hwp.le.trans ((min_le_left _ _).trans (min_le_right _ _))
  have hεδ : ‖w - p‖ ≤ δ / 2 := hwp.le.trans ((min_le_left _ _).trans (min_le_left _ _))
  have hεc : ‖w - p‖ ≤ c / L := hwp.le.trans (min_le_right _ _)
  constructor
  · have hwn : 1 - δ / 2 ≤ ‖w‖ := by
      have h := norm_sub_norm_le p w
      rw [norm_sub_rev] at h
      rw [hpn] at h
      linarith
    rw [← norm_sq_eq]
    rcases le_or_gt δ 2 with h2 | h2
    · have h0 : (0 : ℝ) ≤ 1 - δ / 2 := by linarith
      nlinarith [pow_le_pow_left₀ h0 hwn 2, sq_nonneg δ]
    · nlinarith [sq_nonneg ‖w‖]
  · have hlip := re_pow_lip (k := k) hpn hε1
    have habs := (abs_le.mp hlip).2
    have hmul : L * ‖w - p‖ ≤ L * (c / L) := mul_le_mul_of_nonneg_left hεc hL.le
    rw [mul_div_cancel₀ c hL.ne'] at hmul
    rw [← hLdef] at habs
    linarith

/-! ### The cut-off -/

/-- For `δ > 0`, the radial profile is `0` for `‖w‖² ≤ 1−2δ`, `1` for `‖w‖² ≥ 1−δ`. -/
def aRad (δ : ℝ) (w : ℂ) : ℝ :=
  Real.smoothTransition ((w.re ^ 2 + w.im ^ 2 - (1 - 2 * δ)) / δ)

/-- For `c > 0`, the angular profile is `1` where `Re(w^k) ≤ c`, `0` where `Re(w^k) ≥ 2c`. -/
def bAng (k : ℕ) (c : ℝ) (w : ℂ) : ℝ :=
  Real.smoothTransition ((2 * c - (w ^ k).re) / c)

/-- **The slit cut-off**, for `δ > 0` and `c > 0`: `≡ 0` on `{‖w‖² ≥ 1−δ, Re(w^k) ≤ c}` (containing a neighborhood of the closed
slit when `k ≥ 1`), `≡ 1` where `‖w‖² ≤ 1−2δ` or `Re(w^k) ≥ 2c`. -/
def cutSlit (k : ℕ) (δ c : ℝ) (w : ℂ) : ℝ := 1 - aRad δ w * bAng k c w

lemma aRad_one {δ : ℝ} (hδ : 0 < δ) {w : ℂ} (h : 1 - δ ≤ w.re ^ 2 + w.im ^ 2) :
    aRad δ w = 1 := by
  apply Real.smoothTransition.one_of_one_le
  rw [le_div_iff₀ hδ]
  linarith

lemma bAng_one {c : ℝ} (hc : 0 < c) {w : ℂ} (h : (w ^ k).re ≤ c) : bAng k c w = 1 := by
  apply Real.smoothTransition.one_of_one_le
  rw [le_div_iff₀ hc]
  linarith

/-- The cut-off vanishes on the slit collar. -/
lemma cutSlit_zero {δ c : ℝ} (hδ : 0 < δ) (hc : 0 < c) {w : ℂ}
    (h1 : 1 - δ ≤ w.re ^ 2 + w.im ^ 2) (h2 : (w ^ k).re ≤ c) : cutSlit k δ c w = 0 := by
  rw [cutSlit, aRad_one hδ h1, bAng_one hc h2]
  ring

/-- The cut-off is `1` away from the collar. -/
lemma cutSlit_one {δ c : ℝ} (hδ : 0 < δ) (hc : 0 < c) {w : ℂ}
    (h : w.re ^ 2 + w.im ^ 2 ≤ 1 - 2 * δ ∨ 2 * c ≤ (w ^ k).re) : cutSlit k δ c w = 1 := by
  rcases h with h | h
  · have h0 : aRad δ w = 0 := Real.smoothTransition.zero_of_nonpos
      (div_nonpos_of_nonpos_of_nonneg (by linarith) hδ.le)
    rw [cutSlit, h0, zero_mul, sub_zero]
  · have h0 : bAng k c w = 0 := Real.smoothTransition.zero_of_nonpos
      (div_nonpos_of_nonpos_of_nonneg (by linarith) hc.le)
    rw [cutSlit, h0, mul_zero, sub_zero]

lemma aRad_mem_Icc (δ : ℝ) (w : ℂ) : aRad δ w ∈ Icc (0 : ℝ) 1 :=
  ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩

lemma bAng_mem_Icc (k : ℕ) (c : ℝ) (w : ℂ) : bAng k c w ∈ Icc (0 : ℝ) 1 :=
  ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩

lemma cutSlit_mem_Icc (k : ℕ) (δ c : ℝ) (w : ℂ) : cutSlit k δ c w ∈ Icc (0 : ℝ) 1 := by
  obtain ⟨ha, ha1⟩ := aRad_mem_Icc δ w
  obtain ⟨hb, hb1⟩ := bAng_mem_Icc k c w
  constructor
  · rw [cutSlit]
    nlinarith [mul_le_one₀ ha1 hb hb1]
  · rw [cutSlit]
    nlinarith [mul_nonneg ha hb]

/-! ### Smoothness -/

lemma contDiff_base : ContDiff ℝ ∞ (fun w : ℂ => w.re ^ 2 + w.im ^ 2) := by
  have hre : ContDiff ℝ ∞ (fun w : ℂ => w.re) := Complex.reCLM.contDiff
  have him : ContDiff ℝ ∞ (fun w : ℂ => w.im) := Complex.imCLM.contDiff
  exact (hre.pow 2).add (him.pow 2)

lemma contDiff_repow (k : ℕ) : ContDiff ℝ ∞ (fun w : ℂ => (w ^ k).re) := by
  have hpow : ContDiff ℝ ∞ (fun w : ℂ => w ^ k) := contDiff_id.pow k
  exact Complex.reCLM.contDiff.comp hpow

lemma contDiff_aRad (δ : ℝ) : ContDiff ℝ ∞ (aRad δ) :=
  Real.smoothTransition.contDiff.comp ((contDiff_base.sub contDiff_const).div_const δ)

lemma contDiff_bAng (k : ℕ) (c : ℝ) : ContDiff ℝ ∞ (bAng k c) :=
  Real.smoothTransition.contDiff.comp ((contDiff_const.sub (contDiff_repow k)).div_const c)

lemma contDiff_cutSlit (k : ℕ) (δ c : ℝ) : ContDiff ℝ ∞ (cutSlit k δ c) :=
  contDiff_const.sub ((contDiff_aRad δ).mul (contDiff_bAng k c))

/-! ### The ground-state profile in the smooth chart variable -/

/-- A smooth radial profile, equal to `gRad k 0 ‖w‖` for `k ≥ 1` by `groundR_eq`. -/
def groundR (k : ℕ) (w : ℂ) : ℝ :=
  (kap k - kap k * (w.re ^ 2 + w.im ^ 2) ^ (k - 1)) / ((w.re ^ 2 + w.im ^ 2) ^ (k - 1) + 1)

lemma groundR_denom_pos (k : ℕ) (w : ℂ) :
    0 < (w.re ^ 2 + w.im ^ 2) ^ (k - 1) + 1 := by positivity

lemma contDiff_groundR (k : ℕ) : ContDiff ℝ ∞ (groundR k) :=
  (contDiff_const.sub (contDiff_const.mul (contDiff_base.pow (k - 1)))).div
    ((contDiff_base.pow (k - 1)).add contDiff_const)
    (fun w => (groundR_denom_pos k w).ne')

/-- `groundR` is the radial ground state. -/
lemma groundR_eq (hk : 1 ≤ k) (w : ℂ) : groundR k w = gRad k 0 ‖w‖ := by
  rw [gRad]
  have h1 : ‖w‖ ^ (2 * k - 2) = (w.re ^ 2 + w.im ^ 2) ^ (k - 1) := by
    rw [show 2 * k - 2 = 2 * (k - 1) by omega, pow_mul, norm_sq_eq]
  rw [h1, groundR]
  congr 1
  push_cast
  ring

/-! ### Rotation invariance -/

lemma base_rot {a : ℂ} (ha : ‖a‖ = 1) (w : ℂ) :
    (a * w).re ^ 2 + (a * w).im ^ 2 = w.re ^ 2 + w.im ^ 2 := by
  rw [← norm_sq_eq, ← norm_sq_eq, norm_mul, ha, one_mul]

lemma cutSlit_rot {a : ℂ} (ha : ‖a‖ = 1) (hak : a ^ k = 1) (δ c : ℝ) (w : ℂ) :
    cutSlit k δ c (a * w) = cutSlit k δ c w := by
  unfold cutSlit aRad bAng
  rw [base_rot ha, mul_pow, hak, one_mul]

lemma groundR_rot {a : ℂ} (ha : ‖a‖ = 1) (w : ℂ) : groundR k (a * w) = groundR k w := by
  unfold groundR
  rw [base_rot ha]

/-! ### The class-0 mixed test function -/

/-- **The class-0 mixed (Zaremba) test function**: the slit cut-off times the `ℓ = 0` ground
state, truncated to the closed disk. -/
def zModeCut (k : ℕ) (δ c : ℝ) (w : ℂ) : ℂ :=
  if ‖w‖ ≤ 1 then ((cutSlit k δ c w * groundR k w : ℝ) : ℂ) else 0

lemma zModeCut_eq_of_mem {δ c : ℝ} {w : ℂ} (hw : w ∈ disk) :
    zModeCut k δ c w = ((cutSlit k δ c w * groundR k w : ℝ) : ℂ) := by
  have h1 : ‖w‖ < 1 := mem_disk_iff.mp hw
  simp [zModeCut, h1.le]

/-- The value on the disk, in radial form. -/
lemma zModeCut_on_disk (hk : 1 ≤ k) {δ c : ℝ} {w : ℂ} (hw : w ∈ disk) :
    zModeCut k δ c w = ((cutSlit k δ c w * gRad k 0 ‖w‖ : ℝ) : ℂ) := by
  rw [zModeCut_eq_of_mem hw, groundR_eq hk]

lemma contDiff_zModeF (k : ℕ) (δ c : ℝ) :
    ContDiff ℝ ∞ (fun w => ((cutSlit k δ c w * groundR k w : ℝ) : ℂ)) :=
  Complex.ofRealCLM.contDiff.comp ((contDiff_cutSlit k δ c).mul (contDiff_groundR k))

/-- **Membership in the natural mixed space** (Neumann on `arc_1`, Dirichlet on `arc_0`). -/
theorem zModeCut_mem_NatCc (hk : 1 ≤ k) {δ c : ℝ} (hδ : 0 < δ) (hc : 0 < c) :
    zModeCut k δ c ∈ NatCc k true false := by
  have hF := contDiff_zModeF k δ c
  have hone : ∀ w₀, OneSided (zModeCut k δ c) w₀ := fun w₀ =>
    ⟨_, hF.contDiffAt, Eventually.of_forall fun w hw => zModeCut_eq_of_mem hw⟩
  obtain ⟨ε, hε, hnb⟩ := slit_nbhd hk hδ hc
  have hvan : ∀ w : ℂ, (∃ p ∈ slit k, ‖w - p‖ < ε) → zModeCut k δ c w = 0 := by
    intro w hw
    obtain ⟨h1, h2⟩ := hnb w hw
    unfold zModeCut
    split_ifs
    · rw [cutSlit_zero hδ hc h1 h2, zero_mul, Complex.ofReal_zero]
    · rfl
  rw [mem_NatCc]
  refine ⟨hF.contDiffOn.congr fun w hw => zModeCut_eq_of_mem hw,
    fun w _ => hone w,
    ⟨ε, hε, hvan⟩,
    fun w hw => by simp [zModeCut, not_le.mpr hw],
    ⟨ε, hε, fun w ⟨p, hp, hwp⟩ =>
      hvan w ⟨p, KsIndex.Bracket.punctures_subset_slit hk hp, hwp⟩⟩⟩

lemma zModeCut_rot (hk : 1 ≤ k) (δ c : ℝ) :
    rot1 (rotUnit k : ℂ) (zModeCut k δ c) = zModeCut k δ c := by
  funext w
  have ha : ‖(rotUnit k : ℂ)‖ = 1 := Circle.norm_coe _
  have hak : (rotUnit k : ℂ) ^ k = 1 := rotUnit_pow (by omega)
  simp only [rot1_apply, zModeCut, norm_mul, ha, one_mul]
  rw [cutSlit_rot ha hak, groundR_rot ha]

/-- The test function lies in the trivial rotation class. -/
theorem zModeCut_mem_Erot1 (hk : 1 ≤ k) (δ c : ℝ) : zModeCut k δ c ∈ Erot1 k 0 := by
  rw [Erot1, Module.End.mem_eigenspace_iff, zModeCut_rot hk]
  simp

/-- For `k ≥ 1` and positive cutoff parameters, the cutoff radial profile is a
class-0 mixed natural test function. -/
theorem zModeCut_mem (hk : 1 ≤ k) {δ c : ℝ} (hδ : 0 < δ) (hc : 0 < c) :
    zModeCut k δ c ∈ NatCc k true false ⊓ Erot1 k 0 :=
  Submodule.mem_inf.mpr ⟨zModeCut_mem_NatCc hk hδ hc, zModeCut_mem_Erot1 hk δ c⟩

end KsIndex.SingleDisk
