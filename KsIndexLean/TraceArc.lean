module

/-
# Boundary traces in the arc coefficient space

For `1 ≤ k` and `r ≤ k`, the boundary trace of a field in
`NatCc k true false ⊓ Erot1 k r` is fixed by `convS₁`. Together with the weighted
summability theorem in `MixedUpper`, this gives `MemArc` for `k ≥ 3` and
`1 ≤ r ≤ k - 1`, and then the mixed seam index bound `seamNat k true false r ≤ 1`.

Write `G = extChoice hk1 u` and `h = slice G 1`. The compressed angular function
`W x = exp(−i(k−r)x/k) · h(x/k)` has Fourier coefficients `traceFull hk1 r u`.
The coefficient identity uses the change of variables `x = kθ` and the `k`-fold
period sum of `h(θ) · exp(−i(kn+(k−r))θ)`. Vanishing near the Dirichlet slit gives
some `δ > 0` such that `W x = 0` whenever `cos x < δ`, so
`ArcBridge.convS₁_fc_eq` fixes these coefficients.

The extension agrees with `u` only on the open disk. Boundary equivariance is
obtained by continuity and closure; boundary vanishing follows by radial limits.
The final index comparison uses nonnegativity of `Qd` on the trace kernel and the
circle index theorem, without requiring injectivity of the trace on all fields.
-/
public import KsIndexLean.MixedUpper
public import KsIndexLean.ArcBridge

@[expose] public section


noncomputable section

open Complex Real MeasureTheory intervalIntegral Set Filter Topology
open KsIndex.Parseval KsIndex.FourierMode KsIndex.Surface KsIndex.SingleDisk
  KsIndex.SeamUpper KsIndex.ArcSpace KsIndex.ArcBridge KsIndex.MixedUpper
  KsIndex.SurfaceSym KsIndex.FormIndex KsIndex.Bracket KsIndex.ArcForm KsIndex.ArcLower
  KsIndex.ArcMain

namespace KsIndex.TraceArc

variable {k : ℕ}

/-! ### The `k`-fold period sum -/

/-- `∫₀^{nT} φ = n • ∫₀^T φ` for a continuous `T`-periodic `φ`. -/
lemma integral_nsmul_period {φ : ℝ → ℂ} (hφc : Continuous φ) {T : ℝ}
    (hT : Function.Periodic φ T) (n : ℕ) :
    (∫ x in (0:ℝ)..(n:ℝ) * T, φ x) = (n : ℝ) • ∫ x in (0:ℝ)..T, φ x := by
  induction n with
  | zero => simp
  | succ m ih =>
    have hsplit : (∫ x in (0:ℝ)..((m:ℝ)+1)*T, φ x)
        = (∫ x in (0:ℝ)..(m:ℝ)*T, φ x) + ∫ x in ((m:ℝ)*T)..((m:ℝ)+1)*T, φ x :=
      (integral_add_adjacent_intervals
        (hφc.intervalIntegrable _ _) (hφc.intervalIntegrable _ _)).symm
    have hper : (∫ x in ((m:ℝ)*T)..((m:ℝ)+1)*T, φ x) = ∫ x in (0:ℝ)..T, φ x := by
      have h := hT.intervalIntegral_add_eq ((m:ℝ)*T) 0
      rw [zero_add] at h
      rw [show ((m:ℝ)+1)*T = (m:ℝ)*T + T by ring]
      exact h
    rw [Nat.cast_succ, hsplit, hper, ih, add_smul, one_smul]

/-! ### Boundary equivariance of the extension (via continuity/density) -/

/-- The extension `G = extChoice u` inherits `u`'s class-`r` rotation equivariance on the boundary
sphere: `G(ζ⁻¹ w) = ζ^r G(w)` for `‖w‖ = 1`.  `G = u` only on the OPEN disk, so this is obtained
by `Set.EqOn.closure` (both sides continuous, agreeing on `ball 0 1`, extended to `closedBall`). -/
lemma extChoice_bdry_rotEq {b₁ b₀ : Bool} (hk1 : 1 ≤ k) {r : ℕ}
    (u : ↥(NatCc k b₁ b₀ ⊓ Erot1 k r)) {w : ℂ} (hw : ‖w‖ = 1) :
    extChoice hk1 u ((rotUnit k : ℂ) * w) = (zeta k) ^ r * extChoice hk1 u w := by
  set G := extChoice hk1 u with hGdef
  have hu : (u : ℂ → ℂ) ∈ Erot1 k r := (Submodule.mem_inf.mp u.2).2
  have hGeq : ∀ z ∈ disk, (u : ℂ → ℂ) z = G z := extChoice_eqOn hk1 u
  have hGcont : Continuous G := (extChoice_contDiff hk1 u).continuous
  have hrn : ‖(rotUnit k : ℂ)‖ = 1 := Circle.norm_coe _
  have hEqOn : Set.EqOn (fun z => G ((rotUnit k : ℂ) * z))
      (fun z => (zeta k) ^ r * G z) (Metric.ball (0:ℂ) 1) := by
    intro z hz
    have hz' : ‖z‖ < 1 := by rwa [Metric.mem_ball, dist_zero_right] at hz
    have hzd : z ∈ disk := by rw [disk, Metric.mem_ball, dist_zero_right]; exact hz'
    have hrzd : (rotUnit k : ℂ) * z ∈ disk := by
      rw [disk, Metric.mem_ball, dist_zero_right, norm_mul, hrn, one_mul]; exact hz'
    show G ((rotUnit k : ℂ) * z) = (zeta k) ^ r * G z
    rw [← hGeq _ hrzd, ← hGeq _ hzd]
    exact rotEq_of_mem hu z
  have hc1 : Continuous (fun z => G ((rotUnit k : ℂ) * z)) :=
    hGcont.comp (continuous_const.mul continuous_id)
  have hc2 : Continuous (fun z => (zeta k) ^ r * G z) := continuous_const.mul hGcont
  have hcl := hEqOn.closure hc1 hc2
  rw [closure_ball (0:ℂ) (by norm_num : (1:ℝ) ≠ 0)] at hcl
  exact hcl (by rw [Metric.mem_closedBall, dist_zero_right]; exact le_of_eq hw)

/-- The `2π/k`-shift of the boundary trace `slice G 1` (the `slice_shift` identity for the
extension, via `extChoice_bdry_rotEq`). -/
lemma slice_ext_shift {b₁ b₀ : Bool} (hk1 : 1 ≤ k) {r : ℕ}
    (u : ↥(NatCc k b₁ b₀ ⊓ Erot1 k r)) (θ : ℝ) :
    slice (extChoice hk1 u) 1 (θ + 2 * π / k)
      = (zeta k ^ r)⁻¹ * slice (extChoice hk1 u) 1 θ := by
  have hz : (zeta k) ^ r ≠ 0 := pow_ne_zero _ (by rw [zeta]; exact Complex.exp_ne_zero _)
  have hpt : (rotUnit k : ℂ) * (((1:ℝ) : ℂ) * Complex.exp (((θ + 2 * π / k : ℝ) : ℂ) * I))
      = ((1:ℝ) : ℂ) * Complex.exp ((θ : ℂ) * I) := by
    rw [rotUnit, Circle.coe_exp]
    rw [show ((θ + 2 * π / k : ℝ) : ℂ) * I
      = (θ : ℂ) * I + ((2 * π / k : ℝ) : ℂ) * I by push_cast; ring, Complex.exp_add]
    rw [show ((-(2 * π) / k : ℝ) : ℂ) * I = -(((2 * π / k : ℝ) : ℂ) * I) by push_cast; ring]
    rw [Complex.exp_neg,
      show (Complex.exp (((2 * π / k : ℝ) : ℂ) * I))⁻¹
          * (((1:ℝ) : ℂ) * (Complex.exp ((θ : ℂ) * I) * Complex.exp (((2 * π / k : ℝ) : ℂ) * I)))
        = ((1:ℝ) : ℂ) * Complex.exp ((θ : ℂ) * I)
            * ((Complex.exp (((2 * π / k : ℝ) : ℂ) * I))⁻¹
                * Complex.exp (((2 * π / k : ℝ) : ℂ) * I)) by ring,
      inv_mul_cancel₀ (Complex.exp_ne_zero _), mul_one]
  have hbw : ‖((1:ℝ) : ℂ) * Complex.exp (((θ + 2 * π / k : ℝ) : ℂ) * I)‖ = 1 := by
    rw [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one]; simp
  have hrot := extChoice_bdry_rotEq hk1 u hbw
  rw [hpt] at hrot
  unfold slice
  rw [hrot, ← mul_assoc, inv_mul_cancel₀ hz, one_mul]

/-! ### Arc-vanishing of the boundary trace (Dirichlet slit + density) -/

/-- `G = extChoice u` vanishes at a boundary point lying in the open `ε`-neighborhood of the
Dirichlet slit.  `G = u` only on the OPEN disk, so the boundary value is recovered as the radial
limit `s·w₀ → w₀` (`s ↑ 1`): each `s·w₀` (`s ∈ (0,1)`) is in the disk AND, eventually, in the open
neighborhood, where `G = u = 0`. -/
lemma extChoice_bdry_vanish {b₁ b₀ : Bool} (hk1 : 1 ≤ k) {r : ℕ}
    (u : ↥(NatCc k b₁ b₀ ⊓ Erot1 k r)) {ε : ℝ}
    (hvan : ∀ w : ℂ, (∃ p ∈ slit k, ‖w - p‖ < ε) → (u : ℂ → ℂ) w = 0)
    {w₀ : ℂ} (hw₀ : ‖w₀‖ = 1) (hw₀O : ∃ p ∈ slit k, ‖w₀ - p‖ < ε) :
    extChoice hk1 u w₀ = 0 := by
  set G := extChoice hk1 u with hGdef
  have hGcont : Continuous G := (extChoice_contDiff hk1 u).continuous
  have hGeq : ∀ z ∈ disk, (u : ℂ → ℂ) z = G z := extChoice_eqOn hk1 u
  have hOopen : IsOpen {w : ℂ | ∃ p ∈ slit k, ‖w - p‖ < ε} := by
    have heq : {w : ℂ | ∃ p ∈ slit k, ‖w - p‖ < ε} = ⋃ p ∈ slit k, Metric.ball p ε := by
      ext w; simp only [Set.mem_setOf_eq, Set.mem_iUnion, Metric.mem_ball, dist_eq_norm,
        exists_prop]
    rw [heq]; exact isOpen_biUnion (fun p _ => Metric.isOpen_ball)
  have htend : Tendsto (fun s : ℝ => (s : ℂ) * w₀) (𝓝[<] (1:ℝ)) (𝓝 w₀) := by
    have hc : Continuous (fun s : ℝ => (s : ℂ) * w₀) :=
      Complex.continuous_ofReal.mul continuous_const
    have h : Tendsto (fun s : ℝ => (s : ℂ) * w₀) (𝓝[<] (1:ℝ)) (𝓝 (((1:ℝ) : ℂ) * w₀)) :=
      (hc.tendsto 1).mono_left nhdsWithin_le_nhds
    simpa using h
  have hGtend : Tendsto (fun s : ℝ => G ((s : ℂ) * w₀)) (𝓝[<] (1:ℝ)) (𝓝 (G w₀)) :=
    (hGcont.tendsto w₀).comp htend
  have hev : ∀ᶠ s : ℝ in 𝓝[<] (1:ℝ), G ((s : ℂ) * w₀) = 0 := by
    have hev1 : ∀ᶠ s : ℝ in 𝓝[<] (1:ℝ), (0:ℝ) < s := by
      have h1 : Set.Ioi (0:ℝ) ∈ 𝓝 (1:ℝ) := isOpen_Ioi.mem_nhds (by norm_num)
      filter_upwards [nhdsWithin_le_nhds h1] with s hs; exact hs
    have hev2 : ∀ᶠ s : ℝ in 𝓝[<] (1:ℝ), s < 1 := by
      filter_upwards [self_mem_nhdsWithin] with s hs; exact hs
    have hev3 : ∀ᶠ s : ℝ in 𝓝[<] (1:ℝ),
        (s : ℂ) * w₀ ∈ {w : ℂ | ∃ p ∈ slit k, ‖w - p‖ < ε} :=
      htend.eventually (hOopen.mem_nhds hw₀O)
    filter_upwards [hev1, hev2, hev3] with s hs0 hs1 hsO
    have hball : (s : ℂ) * w₀ ∈ disk := by
      rw [disk, Metric.mem_ball, dist_zero_right, norm_mul, hw₀, mul_one, Complex.norm_real,
        Real.norm_eq_abs, abs_of_pos hs0]
      exact hs1
    rw [← hGeq _ hball]
    exact hvan _ hsO
  have h0 : Tendsto (fun s : ℝ => G ((s : ℂ) * w₀)) (𝓝[<] (1:ℝ)) (𝓝 0) :=
    (tendsto_congr' hev).mpr tendsto_const_nhds
  exact tendsto_nhds_unique hGtend h0

/-- **The boundary trace is arc-supported** (`NatCc k true false`): there is a `δ > 0` such that
`slice G 1 θ = 0` whenever `cos(kθ) < δ`.  The Dirichlet slit `{cos(kθ) ≤ 0}` sits inside the open
`ε`-neighborhood `O` where `G` vanishes (`extChoice_bdry_vanish`); on the compact sphere `Re(w^k)`
is bounded below by a positive `δ` off `O`, so `Re(w^k) = cos(kθ) < δ` forces `exp(iθ) ∈ O`. -/
lemma slice_arc_vanish (hk1 : 1 ≤ k) {r : ℕ}
    (u : ↥(NatCc k true false ⊓ Erot1 k r)) :
    ∃ δ > 0, ∀ θ : ℝ, Real.cos ((k:ℝ) * θ) < δ → slice (extChoice hk1 u) 1 θ = 0 := by
  obtain ⟨_, _, harc0, _, _⟩ := mem_NatCc.mp (Submodule.mem_inf.mp u.2).1
  obtain ⟨ε, hε, hvan⟩ := harc0
  set G := extChoice hk1 u with hGdef
  have hGvan : ∀ w : ℂ, ‖w‖ = 1 → (∃ p ∈ slit k, ‖w - p‖ < ε) → G w = 0 :=
    fun w hw hwO => extChoice_bdry_vanish hk1 u hvan hw hwO
  set O : Set ℂ := {w : ℂ | ∃ p ∈ slit k, ‖w - p‖ < ε} with hOdef
  have hOopen : IsOpen O := by
    have heq : O = ⋃ p ∈ slit k, Metric.ball p ε := by
      ext w; simp only [hOdef, Set.mem_setOf_eq, Set.mem_iUnion, Metric.mem_ball, dist_eq_norm,
        exists_prop]
    rw [heq]; exact isOpen_biUnion (fun p _ => Metric.isOpen_ball)
  set S : Set ℂ := Metric.sphere (0:ℂ) 1 with hSdef
  have hScompact : IsCompact S := isCompact_sphere 0 1
  set K : Set ℂ := S ∩ Oᶜ with hKdef
  have hKcompact : IsCompact K := hScompact.inter_right hOopen.isClosed_compl
  have hReK : ∀ w ∈ K, 0 < (w ^ k).re := by
    intro w hwK
    obtain ⟨hwS, hwO⟩ := hwK
    by_contra hle
    push_neg at hle
    refine hwO ?_
    have hwnorm : ‖w‖ = 1 := by rw [hSdef, mem_sphere_iff_norm, sub_zero] at hwS; exact hwS
    exact ⟨w, ⟨hwnorm, hle⟩, by simp [hε]⟩
  have hcont : ContinuousOn (fun w : ℂ => (w ^ k).re) K :=
    (Complex.continuous_re.comp (continuous_pow k)).continuousOn
  obtain ⟨δ, hδpos, hSO⟩ : ∃ δ > 0, ∀ w ∈ S, (w ^ k).re < δ → w ∈ O := by
    rcases K.eq_empty_or_nonempty with hKe | hKne
    · refine ⟨1, one_pos, fun w hwS _ => ?_⟩
      by_contra hwO
      have hwK : w ∈ K := ⟨hwS, hwO⟩
      rw [hKe] at hwK
      simp at hwK
    · obtain ⟨w₀, hw₀K, hw₀min⟩ := hKcompact.exists_isMinOn hKne hcont
      refine ⟨(w₀ ^ k).re, hReK w₀ hw₀K, fun w hwS hwlt => ?_⟩
      by_contra hwO
      exact absurd (hw₀min (Set.mem_inter hwS hwO)) (not_le.mpr hwlt)
  refine ⟨δ, hδpos, fun θ hθ => ?_⟩
  have hnorm : ‖Complex.exp ((θ : ℂ) * I)‖ = 1 := Complex.norm_exp_ofReal_mul_I θ
  have hwS : Complex.exp ((θ : ℂ) * I) ∈ S := by
    rw [hSdef, mem_sphere_iff_norm, sub_zero]; exact hnorm
  have hwre : (Complex.exp ((θ : ℂ) * I) ^ k).re = Real.cos ((k : ℝ) * θ) := by
    rw [← Complex.exp_nat_mul,
      show (k : ℂ) * ((θ : ℂ) * I) = (((k : ℝ) * θ : ℝ) : ℂ) * I by push_cast; ring,
      Complex.exp_ofReal_mul_I_re]
  have hwO : Complex.exp ((θ : ℂ) * I) ∈ O := hSO _ hwS (by rw [hwre]; exact hθ)
  have hGw : G (Complex.exp ((θ : ℂ) * I)) = 0 := hGvan _ hnorm hwO
  rw [slice, Complex.ofReal_one, one_mul]
  exact hGw

/-! ### The compressed physical function `W` and its Fourier coefficients -/

/-- The compressed physical function on the circle: `W(x) = e^{−i(k−r)x/k}·(slice G 1)(x/k)`.
For `r ≤ k`, its Fourier coefficients are the class-`r` boundary trace (`fc_Wdesc_eq`).
Continuity and vanishing where `cos x < δ` allow application of `ArcBridge.convS₁_fc_eq`. -/
def Wdesc (hk1 : 1 ≤ k) {r : ℕ} (u : ↥(NatCc k true false ⊓ Erot1 k r)) : ℝ → ℂ :=
  fun x => Complex.exp (Complex.ofReal (-(((k - r : ℕ) : ℝ) / (k : ℝ)) * x) * I)
    * slice (extChoice hk1 u) 1 (x / (k : ℝ))

/-- The boundary trace `slice G 1` is continuous (`G` is the `C¹` extension). -/
lemma slice_ext_continuous (hk1 : 1 ≤ k) {r : ℕ}
    (u : ↥(NatCc k true false ⊓ Erot1 k r)) :
    Continuous (slice (extChoice hk1 u) 1) := by
  have hGcont : Continuous (extChoice hk1 u) := (extChoice_contDiff hk1 u).continuous
  unfold slice
  exact hGcont.comp (by fun_prop)

/-- **The compressed function's Fourier coefficients are the class-`r` trace** (`fc W = t`): the
`x = kθ` change of variables (`integral_comp_mul_left`) plus the `k`-fold period sum
(`integral_nsmul_period`) of the `(2π/k)`-periodic integrand. The character identity uses `r ≤ k`. -/
lemma fc_Wdesc_eq (hk1 : 1 ≤ k) {r : ℕ} (hrk : r ≤ k)
    (u : ↥(NatCc k true false ⊓ Erot1 k r)) (n : ℤ) :
    fc (Wdesc hk1 u) n = traceFull hk1 r u n := by
  have hk0 : 0 < k := by omega
  have hkR : (k : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hkC : (k : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  set ℓ₀ : ℤ := (k : ℤ) * n + ((k - r : ℕ) : ℤ) with hℓ₀def
  have ht : traceFull hk1 r u n = fc (slice (extChoice hk1 u) 1) ℓ₀ := by
    rw [traceFull_apply]; rfl
  rw [ht]; unfold fc; congr 1
  set F : ℝ → ℂ := fun θ => Wdesc hk1 u θ * Complex.exp (-(n : ℂ) * I * (θ : ℂ)) with hFdef
  set φ : ℝ → ℂ :=
    fun θ => slice (extChoice hk1 u) 1 θ * Complex.exp (-(ℓ₀ : ℂ) * I * (θ : ℂ)) with hφdef
  -- (i) the phase algebra `F(kθ) = φ(θ)`
  have hFφ : ∀ θ : ℝ, F ((k : ℝ) * θ) = φ θ := by
    intro θ
    simp only [hFdef, hφdef, Wdesc]
    rw [show ((k : ℝ) * θ) / (k : ℝ) = θ by field_simp, mul_right_comm, ← Complex.exp_add,
      mul_comm]
    congr 2
    rw [hℓ₀def]
    push_cast
    field_simp
    ring
  -- (ii) `φ` is continuous and `(2π/k)`-periodic
  have hφcont : Continuous φ := by
    rw [hφdef]; exact (slice_ext_continuous hk1 u).mul (by fun_prop)
  have hφper : Function.Periodic φ (2 * π / (k : ℝ)) := by
    intro θ
    simp only [hφdef]
    rw [slice_ext_shift, Complex.ofReal_add, mul_add, Complex.exp_add]
    have hc : (zeta k ^ r)⁻¹ * Complex.exp (-(ℓ₀ : ℂ) * I * ((2 * π / (k : ℝ) : ℝ) : ℂ)) = 1 := by
      rw [zeta, ← Complex.exp_nat_mul, ← Complex.exp_neg, ← Complex.exp_add]
      rw [show -((r : ℂ) * (2 * ↑π * I / (k : ℂ))) + -(ℓ₀ : ℂ) * I * ((2 * π / (k : ℝ) : ℝ) : ℂ)
          = ((-(n + 1) : ℤ) : ℂ) * (2 * ↑π * I) by
        rw [hℓ₀def]; push_cast [Nat.cast_sub hrk]; field_simp; ring]
      exact Complex.exp_int_mul_two_pi_mul_I _
    rw [show (zeta k ^ r)⁻¹ * slice (extChoice hk1 u) 1 θ
          * (Complex.exp (-(ℓ₀ : ℂ) * I * (θ : ℂ))
              * Complex.exp (-(ℓ₀ : ℂ) * I * ((2 * π / (k : ℝ) : ℝ) : ℂ)))
        = slice (extChoice hk1 u) 1 θ * Complex.exp (-(ℓ₀ : ℂ) * I * (θ : ℂ))
          * ((zeta k ^ r)⁻¹ * Complex.exp (-(ℓ₀ : ℂ) * I * ((2 * π / (k : ℝ) : ℝ) : ℂ))) by ring,
      hc, mul_one]
  -- (iii) the change of variables + `k`-fold period
  have hcov : (∫ x in (0:ℝ)..(2 * π / (k : ℝ)), F ((k : ℝ) * x))
      = (k : ℝ)⁻¹ • ∫ x in (0:ℝ)..2 * π, F x := by
    have h := integral_comp_mul_left F hkR (a := (0:ℝ)) (b := 2 * π / (k : ℝ))
    rwa [mul_zero, show (k : ℝ) * (2 * π / (k : ℝ)) = 2 * π by field_simp] at h
  have hchain : (∫ θ in (0:ℝ)..2 * π, F θ)
      = (k : ℝ) • ∫ x in (0:ℝ)..(2 * π / (k : ℝ)), F ((k : ℝ) * x) := by
    rw [hcov, smul_smul, mul_inv_cancel₀ hkR, one_smul]
  rw [hchain, show (fun x => F ((k : ℝ) * x)) = φ from funext hFφ]
  rw [← integral_nsmul_period hφcont hφper k,
    show ((k : ℕ) : ℝ) * (2 * π / (k : ℝ)) = 2 * π by field_simp]

/-- `W` is continuous. -/
lemma Wdesc_continuous (hk1 : 1 ≤ k) {r : ℕ} (u : ↥(NatCc k true false ⊓ Erot1 k r)) :
    Continuous (Wdesc hk1 u) := by
  unfold Wdesc
  have h1 : Continuous
      (fun x : ℝ => Complex.exp (Complex.ofReal (-(((k - r : ℕ) : ℝ) / (k : ℝ)) * x) * I)) := by
    fun_prop
  have h2 : Continuous (fun x : ℝ => slice (extChoice hk1 u) 1 (x / (k : ℝ))) :=
    (slice_ext_continuous hk1 u).comp (by fun_prop)
  exact h1.mul h2

/-! ### Arc membership: `ς₁·` fixes the trace, and `MemArc (traceFull u)` -/

/-- **The transported trace is fixed by the arc convolution** (`convS₁ t = t`): via
`convS₁_fc_eq` on `W = Wdesc u`, which is continuous (`Wdesc_continuous`), arc-supported in
`cos x` (`slice_arc_vanish` under the `x = kθ` alignment), and has `fc W = t` (`fc_Wdesc_eq`). -/
lemma traceFull_convS₁_fixed (hk1 : 1 ≤ k) {r : ℕ} (hrk : r ≤ k)
    (u : ↥(NatCc k true false ⊓ Erot1 k r)) (m : ℤ) :
    convS₁ (traceFull hk1 r u) m = traceFull hk1 r u m := by
  have hfW : fc (Wdesc hk1 u) = traceFull hk1 r u :=
    funext (fun n => fc_Wdesc_eq hk1 hrk u n)
  obtain ⟨δ, hδpos, hslicevan⟩ := slice_arc_vanish hk1 u
  have hWsupp : ∀ x : ℝ, Real.cos x < δ → Wdesc hk1 u x = 0 := by
    intro x hx
    have hkx : (k : ℝ) * (x / (k : ℝ)) = x := by
      field_simp
    have hs0 : slice (extChoice hk1 u) 1 (x / (k : ℝ)) = 0 :=
      hslicevan (x / (k : ℝ)) (by rw [hkx]; exact hx)
    unfold Wdesc; rw [hs0, mul_zero]
  have hβ : convS₁ (fc (Wdesc hk1 u)) = fc (Wdesc hk1 u) :=
    convS₁_fc_eq (Wdesc hk1 u) (Wdesc_continuous hk1 u) hδpos hWsupp
  rw [← hfW, hβ]

/-- **`MemArc (traceFull hk1 r u)`** for `k ≥ 3` and `1 ≤ r ≤ k - 1`: the two
halves of `MemArc` — the `H^{1/2}` weight (`traceFull_weight_summable`) and the arc-fixing
(`traceFull_convS₁_fixed`). -/
lemma traceFull_memArc (hk : 3 ≤ k) (hk1 : 1 ≤ k) {r : ℕ} (hr1 : 1 ≤ r) (hrk : r ≤ k - 1)
    (u : ↥(NatCc k true false ⊓ Erot1 k r)) :
    MemArc (traceFull hk1 r u) :=
  ⟨traceFull_weight_summable hk hk1 hr1 hrk u,
    traceFull_convS₁_fixed hk1 (by omega) u⟩

/-! ### The mixed middle-class upper bound -/

/-- **The mixed middle-class seam count is at most one** (`k ≥ 3`, `1 ≤ r ≤ k−1`):
`seamNat k true false r ≤ 1`.  The boundary-trace map `traceFull` transports the disk problem
`(NatCc k true false ⊓ Erot1 k r, Qd k)` into the circle model `(ArcDom, N_{(a;k)})` at `a = aOf r k`
— `formIndex_le_of_negMap` with `hmem = traceFull_memArc`, `hneg = NQformArc_neg_of_Qd_neg`,
`hker = qd_nonneg_of_traceFull_zero` — and `m2_circle` gives `ind_DN(N_{(1−r/k;k)}) = 1`. -/
theorem seamNat_mixed_le_one (hk : 3 ≤ k) (hk1 : 1 ≤ k) {r : ℕ} (hr1 : 1 ≤ r) (hrk : r ≤ k - 1) :
    seamNat k true false r ≤ 1 := by
  rw [seamNat]
  refine le_trans (formIndex_le_of_negMap (traceFull hk1 r)
    (fun v => mem_ArcDom.mpr (traceFull_memArc hk hk1 hr1 hrk v))
    (fun v hv => NQformArc_neg_of_Qd_neg hk hk1 hr1 hrk v hv)
    (fun v hv => qd_nonneg_of_traceFull_zero hk hk1 (by omega) v hv)) ?_
  exact le_of_eq (m2_circle hk hr1 hrk).1

end KsIndex.TraceArc
