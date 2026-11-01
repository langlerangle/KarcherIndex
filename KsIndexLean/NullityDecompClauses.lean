module

public import KsIndexLean.NullityDecompCore
public import KsIndexLean.JacobiFamily

@[expose] public section


/-!
# Rotation and seam-reflection preservation of bounded Jacobi fields

`laplacian_comp_mul` proves that the flat Laplacian commutes with multiplication
by a unit complex number, assuming `f` is `C²` in a neighborhood of the image point.
For bounded Jacobi fields, rotation preservation additionally requires `a ^ k = 1`.
Seam-reflection preservation uses `reflF c u n w = u (c - n) w` with
`parity m c = 1`. The proofs preserve smoothness, boundedness, the Jacobi equation,
puncture values, and matching values across seams.

For reflections, the local identity for the glued fields uses
`σ(z) = 1 / conj z`. It holds near a seam point using the matching seam values;
this local transport supplies smoothness across the reflected seam.

Proof of the Laplacian identity: two applications of the existing chain rule
`fderiv_comp_mul` express `Δ(f∘a·)(w)` through the second-derivative pairing
`B v v' := ∂_v ∂_{v'} f (aw)` as `B a a + B (aI) (aI)`; expanding `a = x•1 + y•I`,
`a·I = (−y)•1 + x•I` bilinearly, the cross terms cancel with opposite signs and the
diagonal carries `x² + y² = ‖a‖² = 1` — no second-derivative symmetry is needed.
-/

noncomputable section
namespace KsIndex.NullityDecomp
open KsIndex.Surface KsIndex.SurfaceSym Complex Filter Topology
open scoped ContDiff

/-- **The flat Laplacian commutes with unit rotations.** -/
lemma laplacian_comp_mul {f : ℂ → ℂ} {a w : ℂ} (ha : ‖a‖ = 1)
    (hf : ∀ᶠ y in 𝓝 (a * w), ContDiffAt ℝ 2 f y) :
    laplacian (fun z => f (a * z)) w = laplacian f (a * w) := by
  have hfw : ContDiffAt ℝ 2 f (a * w) := hf.self_of_nhds
  have hc : Continuous fun z : ℂ => a * z := continuous_const.mul continuous_id
  have hten : Tendsto (fun z : ℂ => a * z) (𝓝 w) (𝓝 (a * w)) := hc.continuousAt
  have hdiff : ∀ᶠ z in 𝓝 w, DifferentiableAt ℝ f (a * z) := by
    filter_upwards [hten.eventually hf] with z hz
    exact hz.differentiableAt (by norm_num)
  -- first derivatives transport
  have hfd1 : (fun z => fderiv ℝ (fun y => f (a * y)) z 1) =ᶠ[𝓝 w]
      (fun z => fderiv ℝ f (a * z) a) := by
    filter_upwards [hdiff] with z hz
    rw [fderiv_comp_mul hz, mul_one]
  have hfdI : (fun z => fderiv ℝ (fun y => f (a * y)) z I) =ᶠ[𝓝 w]
      (fun z => fderiv ℝ f (a * z) (a * I)) := by
    filter_upwards [hdiff] with z hz
    rw [fderiv_comp_mul hz]
  have hdd : DifferentiableAt ℝ (fderiv ℝ f) (a * w) :=
    (hfw.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hdv : ∀ v : ℂ, DifferentiableAt ℝ (fun y => fderiv ℝ f y v) (a * w) :=
    fun v => hdd.clm_apply (differentiableAt_const v)
  -- second derivatives transport (chain rule again)
  have h2a : fderiv ℝ (fun z => fderiv ℝ (fun y => f (a * y)) z 1) w 1 =
      fderiv ℝ (fun y => fderiv ℝ f y a) (a * w) a := by
    rw [hfd1.fderiv_eq]
    have h := fderiv_comp_mul (f := fun y => fderiv ℝ f y a) (a := a) (w := w) (hdv a) 1
    rwa [mul_one] at h
  have h2I : fderiv ℝ (fun z => fderiv ℝ (fun y => f (a * y)) z I) w I =
      fderiv ℝ (fun y => fderiv ℝ f y (a * I)) (a * w) (a * I) := by
    rw [hfdI.fderiv_eq]
    exact fderiv_comp_mul (f := fun y => fderiv ℝ f y (a * I)) (a := a) (w := w)
      (hdv (a * I)) I
  -- the second-derivative pairing and its bilinearity
  set B : ℂ → ℂ → ℂ := fun v v' => fderiv ℝ (fun y => fderiv ℝ f y v') (a * w) v with hB
  have hBaddR : ∀ v w₁ w₂ : ℂ, B v (w₁ + w₂) = B v w₁ + B v w₂ := by
    intro v w₁ w₂
    have h1 : DifferentiableAt ℝ (fun y => fderiv ℝ f y w₁) (a * w) := hdv w₁
    have h2 : DifferentiableAt ℝ (fun y => fderiv ℝ f y w₂) (a * w) := hdv w₂
    have he : (fun y => fderiv ℝ f y (w₁ + w₂)) =
        ((fun y => fderiv ℝ f y w₁) + (fun y => fderiv ℝ f y w₂)) := by
      funext y; simp only [Pi.add_apply]; rw [map_add]
    have hkey := fderiv_add h1 h2
    simp only [hB]
    rw [he, hkey]
    simp
  have hBsmulR : ∀ (t : ℝ) (v w₁ : ℂ), B v (t • w₁) = t • B v w₁ := by
    intro t v w₁
    have h1 : DifferentiableAt ℝ (fun y => fderiv ℝ f y w₁) (a * w) := hdv w₁
    have he : (fun y => fderiv ℝ f y (t • w₁)) = t • (fun y => fderiv ℝ f y w₁) := by
      funext y; simp only [Pi.smul_apply]; rw [map_smul]
    have hkey := fderiv_const_smul h1 t
    simp only [hB]
    rw [he, hkey]
    simp
  have hBaddL : ∀ v₁ v₂ w₁ : ℂ, B (v₁ + v₂) w₁ = B v₁ w₁ + B v₂ w₁ := by
    intro v₁ v₂ w₁; simp only [hB, map_add]
  have hBsmulL : ∀ (t : ℝ) (v w₁ : ℂ), B (t • v) w₁ = t • B v w₁ := by
    intro t v w₁; simp only [hB, map_smul]
  have expand : ∀ p q r s : ℝ, B (p • (1 : ℂ) + q • I) (r • (1 : ℂ) + s • I)
      = (p * r) • B 1 1 + (p * s) • B 1 I + (q * r) • B I 1 + (q * s) • B I I := by
    intro p q r s
    rw [hBaddL, hBsmulL, hBsmulL, hBaddR, hBaddR, hBsmulR, hBsmulR, hBsmulR, hBsmulR]
    module
  -- the coordinates of `a`
  have ha1 : a = a.re • (1 : ℂ) + a.im • I := by
    simp only [mul_one, Complex.real_smul]
    exact (Complex.re_add_im a).symm
  have haI : a * I = (-a.im) • (1 : ℂ) + a.re • I := by
    simp only [Complex.real_smul, mul_one, Complex.ofReal_neg]
    rw [Complex.ext_iff]
    constructor <;> simp [Complex.mul_re, Complex.mul_im]
  have hxy : a.re * a.re + a.im * a.im = 1 := by
    have h1 : ‖a‖ ^ 2 = 1 := by rw [ha]; norm_num
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply] at h1
    linarith
  -- assemble
  change fderiv ℝ (fun z => fderiv ℝ (fun y => f (a * y)) z 1) w 1 +
      fderiv ℝ (fun z => fderiv ℝ (fun y => f (a * y)) z I) w I =
      fderiv ℝ (fun z => fderiv ℝ f z 1) (a * w) 1 +
      fderiv ℝ (fun z => fderiv ℝ f z I) (a * w) I
  rw [h2a, h2I]
  have hgoal : B a a + B (a * I) (a * I) = B 1 1 + B I I := by
    have hA := expand a.re a.im a.re a.im
    have hAI := expand (-a.im) a.re (-a.im) a.re
    rw [← ha1] at hA
    rw [← haI] at hAI
    rw [hA, hAI]
    have hcomb : (a.re * a.re) • B 1 1 + (a.re * a.im) • B 1 I + (a.im * a.re) • B I 1 +
        (a.im * a.im) • B I I +
        ((-a.im * -a.im) • B 1 1 + (-a.im * a.re) • B 1 I + (a.re * -a.im) • B I 1 +
        (a.re * a.re) • B I I) =
        ((a.re * a.re + -a.im * -a.im : ℝ)) • B 1 1 + ((a.re * a.im + -a.im * a.re : ℝ)) • B 1 I +
        ((a.im * a.re + a.re * -a.im : ℝ)) • B I 1 + ((a.im * a.im + a.re * a.re : ℝ)) • B I I := by
      module
    rw [hcomb, show (a.re * a.im + -a.im * a.re : ℝ) = 0 by ring,
      show (a.im * a.re + a.re * -a.im : ℝ) = 0 by ring,
      show (a.re * a.re + -a.im * -a.im : ℝ) = 1 by nlinarith [hxy],
      show (a.im * a.im + a.re * a.re : ℝ) = 1 by linarith [hxy]]
    simp
  exact hgoal

/-! ### Rotation invariance of the geometric data -/

lemma pow_two_mul_comp_mul {k : ℕ} {a : ℂ} (hak : a ^ k = 1) (w : ℂ) :
    (a * w) ^ (2 * k) = w ^ (2 * k) := by
  rw [mul_pow, mul_comm 2 k, pow_mul, hak, one_pow, one_mul]

lemma rho_comp_mul {k : ℕ} {a : ℂ} (ha : ‖a‖ = 1) (hak : a ^ k = 1) (w : ℂ) :
    rho k (a * w) = rho k w := by
  unfold rho
  rw [norm_mul, ha, one_mul, pow_two_mul_comp_mul hak]

lemma absA_comp_mul {k : ℕ} {a : ℂ} (ha : ‖a‖ = 1) (hak : a ^ k = 1) (w : ℂ) :
    absA k (a * w) = absA k w := by
  unfold absA
  rw [norm_mul, ha, one_mul, rho_comp_mul ha hak]

/-! ### The rotation stabilizes `BoundedJacobi` -/

lemma rotF_mem_boundedJacobi {k m : ℕ} {a : ℂ} (ha : ‖a‖ = 1) (hak : a ^ k = 1)
    {u : ZMod (2 * m) → ℂ → ℂ} (hu : u ∈ BoundedJacobi k m) :
    rotF a u ∈ BoundedJacobi k m := by
  obtain ⟨⟨hsm1, hsm2, hsm3⟩, hbd, hjac, hpz, hsv⟩ := hu
  have hnorm : ∀ w : ℂ, ‖a * w‖ = ‖w‖ := fun w => by rw [norm_mul, ha, one_mul]
  have hmul : ContDiff ℝ ∞ (fun w : ℂ => a * w) := contDiff_const.mul contDiff_id
  have hconj : ∀ w : ℂ, a * (1 / (starRingEnd ℂ) w) = 1 / (starRingEnd ℂ) (a * w) := by
    intro w
    have h1 : ((starRingEnd ℂ) a)⁻¹ = a :=
      inv_eq_of_mul_eq_one_right (by rw [Complex.conj_mul', ha]; norm_num)
    rw [map_mul, one_div, one_div, mul_inv, h1]
  have harc : ∀ n (w : ℂ), w ∈ seamArc k m n → a * w ∈ seamArc k m n := by
    intro n w hw
    obtain ⟨hw1, hw2⟩ := hw
    refine ⟨by rw [hnorm]; exact hw1, ?_⟩
    rw [mul_pow, hak, one_mul]; exact hw2
  have hdisk : ∀ w : ℂ, w ∈ disk → a * w ∈ disk := by
    intro w hw
    simpa only [disk, Metric.mem_ball, dist_zero_right, hnorm] using hw
  refine ⟨⟨fun n => (hsm1 n).comp hmul.contDiffOn (fun w hw => hdisk w hw),
    fun n w hw => ?_, fun n w hw => hsm3 n (a * w) (by rw [hnorm]; exact hw)⟩,
    ?_, fun n w hw => ?_, fun n p hp => ?_, fun n w hw => hsv n (a * w) (harc n w hw)⟩
  · -- glue smoothness across the seam
    have hglue : glue (rotF a u) n = fun w => glue u n (a * w) := by
      funext z
      simp only [glue, rotF, hnorm, hconj]
    rw [hglue]
    exact (hsm2 n (a * w) (harc n w hw)).comp w hmul.contDiffAt
  · obtain ⟨C, hC⟩ := hbd
    exact ⟨C, fun n w => hC n (a * w)⟩
  · -- the Jacobi equation transports through `laplacian_comp_mul`
    have haw : a * w ∈ disk := hdisk w hw
    have hf2 : ∀ᶠ y in 𝓝 (a * w), ContDiffAt ℝ 2 (u n) y := by
      filter_upwards [(Metric.isOpen_ball).mem_nhds haw] with y hy
      exact ((hsm1 n).contDiffAt ((Metric.isOpen_ball).mem_nhds hy)).of_le two_le_infty
    have hlap : laplacian (rotF a u n) w = laplacian (u n) (a * w) :=
      laplacian_comp_mul ha hf2
    have hjaw := hjac n (a * w) haw
    unfold laplacianG at hjaw ⊢
    rw [rho_comp_mul ha hak w, absA_comp_mul ha hak w] at hjaw
    rw [hlap]
    exact hjaw
  · -- punctures are rotation-invariant
    have hap : a * p ∈ punctures k := by
      change (a * p) ^ (2 * k) = -1
      rw [pow_two_mul_comp_mul hak]
      exact hp
    exact hpz n (a * p) hap

/-! ### The seam reflections stabilize `BoundedJacobi` -/

/-- Curried form of `reflE`: `reflF c u n w = u (c − n) w`. -/
def reflF {m : ℕ} (c : ZMod (2 * m)) (u : ZMod (2 * m) → ℂ → ℂ) : ZMod (2 * m) → ℂ → ℂ :=
  fun n w => u (c - n) w

/-- For odd `c` the reflected seam shares its arc family: `seamArc (c−n−1) = seamArc n`. -/
lemma seamArc_reflIndex {k m : ℕ} {c : ZMod (2 * m)} (hc : parity m c = 1)
    (n : ZMod (2 * m)) : seamArc k m (c - n - 1) = seamArc k m n := by
  unfold seamArc
  have h2 : ∀ x : ZMod 2, 1 - x = x + 1 := by decide
  have hpar : parity m (c - n - 1 + 1) = parity m (n + 1) := by
    rw [sub_add_cancel, map_sub, hc, map_add, map_one]
    exact h2 _
  rw [hpar]

/-- On the unit circle, `σ` is the identity. -/
lemma sigma_circle {z : ℂ} (hz : ‖z‖ = 1) : 1 / (starRingEnd ℂ) z = z := by
  have h : (starRingEnd ℂ) z * z = 1 := by
    rw [mul_comm, Complex.mul_conj]
    norm_cast
    rw [Complex.normSq_eq_norm_sq, hz]
    norm_num
  rw [one_div, inv_eq_of_mul_eq_one_right h]

/-- `σ` is an involution (with Lean's `0⁻¹ = 0` convention, unconditionally). -/
lemma sigma_sigma (z : ℂ) :
    1 / (starRingEnd ℂ) (1 / (starRingEnd ℂ) z) = z := by
  rw [one_div, one_div, map_inv₀, Complex.conj_conj, inv_inv]

lemma norm_sigma (z : ℂ) : ‖1 / (starRingEnd ℂ) z‖ = ‖z‖⁻¹ := by
  rw [one_div, norm_inv, RCLike.norm_conj]

/-- **The reflected glue transport**: near a seam point, `glue (reflF c u) n` agrees with
`glue u (c − n − 1) ∘ σ`. -/
lemma glue_reflF_eventuallyEq {k m : ℕ} {c : ZMod (2 * m)} (hc : parity m c = 1)
    {u : ZMod (2 * m) → ℂ → ℂ} (hsv : SeamVal k u) (n : ZMod (2 * m)) {w : ℂ}
    (hw : w ∈ seamArc k m n) :
    glue (reflF c u) n =ᶠ[𝓝 w] fun z => glue u (c - n - 1) (1 / (starRingEnd ℂ) z) := by
  obtain ⟨hw1, hw2⟩ := hw
  -- circle points near `w` stay inside the (relatively open) seam arc, and `0` stays away
  have hBadC : IsClosed {z : ℂ | ‖z‖ = 1 ∧
      0 ≤ (-1 : ℝ) ^ (parity m (n + 1)).val * (z ^ k).re} := by
    apply IsClosed.inter
    · exact isClosed_eq continuous_norm continuous_const
    · exact isClosed_le continuous_const
        (continuous_const.mul (Complex.continuous_re.comp (continuous_pow k)))
  have hwBad : w ∈ {z : ℂ | ‖z‖ = 1 ∧
      0 ≤ (-1 : ℝ) ^ (parity m (n + 1)).val * (z ^ k).re}ᶜ := by
    intro hmem
    exact absurd hw2 (not_lt.mpr hmem.2)
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hBadC.isOpen_compl w hwBad
  have hnhds : Metric.ball w (min ε (1 / 2)) ∈ 𝓝 w :=
    Metric.ball_mem_nhds w (lt_min hε (by norm_num))
  filter_upwards [hnhds] with z hz
  have hzball : z ∈ Metric.ball w ε :=
    Metric.ball_subset_ball (min_le_left _ _) hz
  have hzhalf : dist z w < 1 / 2 := lt_of_lt_of_le hz (min_le_right _ _)
  have hz0 : z ≠ 0 := by
    intro h0
    rw [h0, dist_comm, dist_zero_right, hw1] at hzhalf
    norm_num at hzhalf
  rcases lt_trichotomy ‖z‖ 1 with h1 | h1 | h1
  · -- strictly inside: both sides read the copy `c − n` value at `z`
    have hσgt : 1 < ‖1 / (starRingEnd ℂ) z‖ := by
      rw [norm_sigma]
      exact (one_lt_inv_iff₀.mpr ⟨norm_pos_iff.mpr hz0, h1⟩)
    unfold glue reflF
    split_ifs with ha hb hb
    · exact absurd hb (not_le.mpr hσgt)
    · rw [sigma_sigma, sub_add_cancel]
    · exact absurd (le_of_lt h1) ha
    · exact absurd (le_of_lt h1) ha
  · -- on the circle: `σ` is the identity and `SeamVal` matches the two copies
    have hzBad := hball hzball
    have hql : (-1 : ℝ) ^ (parity m (n + 1)).val * (z ^ k).re < 0 := by
      by_contra hge
      exact hzBad ⟨h1, not_lt.mp hge⟩
    have hzarc' : z ∈ seamArc k m (c - n - 1) := by
      rw [seamArc_reflIndex hc]
      exact ⟨h1, hql⟩
    have hσz := sigma_circle h1
    have hsv' := hsv (c - n - 1) z hzarc'
    rw [sub_add_cancel] at hsv'
    unfold glue reflF
    rw [hσz]
    split_ifs with ha
    · exact hsv'
    · exact absurd (le_of_eq h1) ha
  · -- strictly outside: both sides read the copy `c − n − 1` value at `σ z`
    have hσlt : ‖1 / (starRingEnd ℂ) z‖ < 1 := by
      rw [norm_sigma]
      exact inv_lt_one_of_one_lt₀ h1
    unfold glue reflF
    split_ifs with ha hb hb
    · exact absurd ha (not_le.mpr h1)
    · exact absurd ha (not_le.mpr h1)
    · congr 1
      ring
    · exact absurd (le_of_lt hσlt) hb

/-- **The seam reflections stabilize `BoundedJacobi`** (odd `c`). -/
lemma reflF_mem_boundedJacobi {k m : ℕ} {c : ZMod (2 * m)} (hc : parity m c = 1)
    {u : ZMod (2 * m) → ℂ → ℂ} (hu : u ∈ BoundedJacobi k m) :
    reflF c u ∈ BoundedJacobi k m := by
  obtain ⟨⟨hsm1, hsm2, hsm3⟩, hbd, hjac, hpz, hsv⟩ := hu
  refine ⟨⟨fun n => hsm1 (c - n), fun n w hw => ?_, fun n w hw => hsm3 (c - n) w hw⟩,
    ?_, fun n w hw => hjac (c - n) w hw, fun n p hp => hpz (c - n) p hp, fun n w hw => ?_⟩
  · -- seam smoothness via the glue transport
    have hev := glue_reflF_eventuallyEq (k := k) hc hsv n hw
    have hw1 : ‖w‖ = 1 := hw.1
    have hw0 : w ≠ 0 := by
      intro h
      rw [h, norm_zero] at hw1
      exact zero_ne_one hw1
    have hσw : (1 / (starRingEnd ℂ) w) = w := sigma_circle hw1
    have hσ : ContDiffAt ℝ ∞ (fun z : ℂ => 1 / (starRingEnd ℂ) z) w := by
      simp only [one_div]
      have hconj : ContDiffAt ℝ ∞ (fun z : ℂ => (starRingEnd ℂ) z) w :=
        Complex.conjCLE.contDiff.contDiffAt
      have hne : (starRingEnd ℂ) w ≠ 0 := by simpa using hw0
      exact (contDiffAt_inv ℝ hne).comp w hconj
    have hmem' : w ∈ seamArc k m (c - n - 1) := by
      rw [seamArc_reflIndex hc]
      exact hw
    have houter : ContDiffAt ℝ ∞ (glue u (c - n - 1)) (1 / (starRingEnd ℂ) w) := by
      rw [hσw]
      exact hsm2 (c - n - 1) w hmem'
    have hcomp := houter.comp w hσ
    rw [Function.comp_def] at hcomp
    exact hcomp.congr_of_eventuallyEq hev
  · obtain ⟨C, hC⟩ := hbd
    exact ⟨C, fun n w => hC (c - n) w⟩
  · -- SeamVal
    have hmem' : w ∈ seamArc k m (c - n - 1) := by
      rw [seamArc_reflIndex hc]
      exact hw
    have h := hsv (c - n - 1) w hmem'
    rw [sub_add_cancel] at h
    change u (c - (n + 1)) w = u (c - n) w
    have he : c - (n + 1) = c - n - 1 := by ring
    rw [he]
    exact h.symm

end KsIndex.NullityDecomp
