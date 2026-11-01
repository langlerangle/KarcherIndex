module

/-
# Jacobi equations in end charts and across seams

For `k ≥ 2`, a geometric Jacobi field satisfies the flat equation
`Δ(u n) + potV k · (u n) = 0` on the open disk. Pullback through
`endChart p m ζ = p + ζ^m` multiplies the potential by the covering Jacobian,
giving `generalEndPotential k p m`; for `k = 3` this is `endPotential p m`.

Reflection in the unit circle preserves the flat equation away from zero:
the Laplacian factor `‖w‖⁻⁴` cancels the potential's factor `‖w‖⁴`.
Thus both direct and reflected chart branches have the same transformed
potential, under their stated regularity and domain hypotheses.

The file also proves the flat equation for `glue u n` in the disk, in the
exterior, and at seam-arc points. At a seam point, `IsSmooth` supplies a
smooth germ, and the continuous equation residual vanishes by approach from
the disk. Local `C²` regularity in the disk and exterior is recorded separately.
Assignment of copy indices to an assembled end field is handled by consumers.
-/
public import KsIndexLean.EndChartLaplacian
public import KsIndexLean.SigmaLaplacian
public import KsIndexLean.JacobiFields
public import KsIndexLean.PotVSigma

@[expose] public section


noncomputable section
open KsIndex.Surface KsIndex.JacobiFields Complex Filter Topology
open scoped ContDiff

namespace KsIndex.EndChart

/-- **Geometric ⇒ flat Jacobi equation on the disk** (the reverse of
`JacobiFields.laplacianG_add_absASq_of_flat`): a geometric Jacobi field solves
the flat equation `Δ(u n) + potV·(u n) = 0` pointwise on the open disk. -/
lemma flat_of_isJacobiField {k m : ℕ} (hk : 2 ≤ k) {u : ZMod (2 * m) → ℂ → ℂ}
    (hjac : IsJacobiField k m u) (n : ZMod (2 * m)) {w : ℂ} (hw : w ∈ disk) :
    laplacian (u n) w + (potV k w : ℂ) * u n w = 0 := by
  have hnp : w ∉ punctures k := punctures_notMem_disk (by omega) hw
  have hρ : (0 : ℝ) < rho k w := rho_pos (by omega) hnp
  have hρ2 : (rho k w ^ 2 : ℝ) ≠ 0 := by positivity
  have hg := hjac n w hw
  have hV : (absA k w ^ 2 : ℝ) = (rho k w ^ 2)⁻¹ * potV k w := by
    field_simp
    linear_combination absA_sq_mul_rho_sq hk hnp
  have hident : laplacianG k (u n) w + ((absA k w ^ 2 : ℝ) : ℂ) * u n w
      = (((rho k w ^ 2)⁻¹ : ℝ) : ℂ) * (laplacian (u n) w + (potV k w : ℂ) * u n w) := by
    rw [laplacianG, hV]; push_cast; ring
  rw [hident] at hg
  have hinv : (((rho k w ^ 2)⁻¹ : ℝ) : ℂ) ≠ 0 := by
    simp only [ne_eq, Complex.ofReal_eq_zero, inv_eq_zero]; exact hρ2
  exact (mul_eq_zero.mp hg).resolve_left hinv

/-- Pullback through the covering chart, with its Jacobian included in the potential. -/
theorem endComp_of_flat_general (k : ℕ) {h : ℂ → ℂ} (p : ℂ) {m : ℕ} {ζ : ℂ}
    (hC2 : ContDiffAt ℝ 2 h (endChart p m ζ))
    (hflat : laplacian h (endChart p m ζ)
      + (potV k (endChart p m ζ) : ℂ) * h (endChart p m ζ) = 0) :
    laplacian (fun z => h (endChart p m z)) ζ
      + (generalEndPotential k p m ζ : ℂ) * h (endChart p m ζ) = 0 := by
  have hpull : laplacian (fun z => h (endChart p m z)) ζ
      = (((m : ℝ) ^ 2 * ‖ζ‖ ^ (2 * (m - 1)) : ℝ) : ℂ) * laplacian h (endChart p m ζ) :=
    laplacian_comp_endChart p m hC2
  have hlap : laplacian h (endChart p m ζ)
      = -(potV k (endChart p m ζ) : ℂ) * h (endChart p m ζ) := by linear_combination hflat
  rw [hpull, hlap, generalEndPotential, endChart]
  rw [pow_mul, Complex.sq_norm]
  push_cast; ring

theorem endComp_of_flat {h : ℂ → ℂ} (p : ℂ) {m : ℕ} {ζ : ℂ}
    (hC2 : ContDiffAt ℝ 2 h (endChart p m ζ))
    (hflat : laplacian h (endChart p m ζ)
      + (potV 3 (endChart p m ζ) : ℂ) * h (endChart p m ζ) = 0) :
    laplacian (fun z => h (endChart p m z)) ζ
      + (endPotential p m ζ : ℂ) * h (endChart p m ζ) = 0 := by
  simpa only [generalEndPotential_three] using
    endComp_of_flat_general 3 p hC2 hflat

/-- **The interior end-chart Jacobi equation.**  Where `σ_c(ζ)` lands strictly
inside the disk, the direct copy `(u n) ∘ σ_c` solves the transformed equation. -/
theorem endComp_jacobi_general {k m : ℕ} (hk : 2 ≤ k) {u : ZMod (2 * m) → ℂ → ℂ}
    (hsm : ∀ n, ContDiffOn ℝ ∞ (u n) disk) (hjac : IsJacobiField k m u)
    (p : ℂ) (n : ZMod (2 * m)) {ζ : ℂ} (hσ : endChart p m ζ ∈ disk) :
    laplacian (fun z => u n (endChart p m z)) ζ
      + (generalEndPotential k p m ζ : ℂ) * u n (endChart p m ζ) = 0 :=
  endComp_of_flat_general k p
    (((hsm n).contDiffAt (Metric.isOpen_ball.mem_nhds hσ)).of_le two_le_infty)
    (flat_of_isJacobiField (k := k) hk hjac n hσ)

theorem endComp_jacobi {m : ℕ} {u : ZMod (2 * m) → ℂ → ℂ}
    (hsm : ∀ n, ContDiffOn ℝ ∞ (u n) disk) (hjac : IsJacobiField 3 m u)
    (p : ℂ) (n : ZMod (2 * m)) {ζ : ℂ} (hσ : endChart p m ζ ∈ disk) :
    laplacian (fun z => u n (endChart p m z)) ζ
      + (endPotential p m ζ : ℂ) * u n (endChart p m ζ) = 0 := by
  simpa only [generalEndPotential_three] using
    endComp_jacobi_general (by norm_num : 2 ≤ 3) hsm hjac p n hσ

/-- Reflection preserves the flat equation: its Laplacian and potential weights cancel. -/
theorem comp_sigma_flat_general {k : ℕ} (hk : 2 ≤ k) {h : ℂ → ℂ} {w : ℂ} (hw0 : w ≠ 0)
    (hC2 : ContDiffAt ℝ 2 h (Bracket.σ w))
    (hflat : laplacian h (Bracket.σ w) + (potV k (Bracket.σ w) : ℂ) * h (Bracket.σ w) = 0) :
    laplacian (h ∘ Bracket.σ) w + (potV k w : ℂ) * (h ∘ Bracket.σ) w = 0 := by
  have hpull := laplacian_comp_sigma hw0 hC2
  have hpv : potV k (Bracket.σ w) = potV k w * ‖w‖ ^ 4 := by
    rw [Bracket.σ_apply]; exact KsIndex.PotVSigma.potV_sigma k hk hw0
  have hnw : ‖w‖ ≠ 0 := norm_ne_zero_iff.mpr hw0
  have hlap : laplacian h (Bracket.σ w)
      = -(potV k (Bracket.σ w) : ℂ) * h (Bracket.σ w) := by linear_combination hflat
  have key : ((‖w‖⁻¹ ^ 4 : ℝ) : ℂ) * ((‖w‖ ^ 4 : ℝ) : ℂ) = 1 := by
    rw [← Complex.ofReal_mul, ← mul_pow, inv_mul_cancel₀ hnw, one_pow, Complex.ofReal_one]
  rw [hpull, hlap, hpv, Complex.ofReal_mul, Function.comp_apply]
  linear_combination (-(potV k w : ℂ) * h (Bracket.σ w)) * key

theorem comp_sigma_flat {h : ℂ → ℂ} {w : ℂ} (hw0 : w ≠ 0)
    (hC2 : ContDiffAt ℝ 2 h (Bracket.σ w))
    (hflat : laplacian h (Bracket.σ w) + (potV 3 (Bracket.σ w) : ℂ) * h (Bracket.σ w) = 0) :
    laplacian (h ∘ Bracket.σ) w + (potV 3 w : ℂ) * (h ∘ Bracket.σ) w = 0 := by
  exact comp_sigma_flat_general (by norm_num : 2 ≤ 3) hw0 hC2 hflat

/-- **The reflected copy solves the SAME flat Jacobi equation** (the special case `h = u j`). -/
theorem reflected_flat_jacobi_general {k m : ℕ} (hk : 2 ≤ k) {u : ZMod (2 * m) → ℂ → ℂ}
    (hsm : ∀ n, ContDiffOn ℝ ∞ (u n) disk) (hjac : IsJacobiField k m u)
    (j : ZMod (2 * m)) {w : ℂ} (hw0 : w ≠ 0) (hwin : Bracket.σ w ∈ disk) :
    laplacian (u j ∘ Bracket.σ) w + (potV k w : ℂ) * (u j ∘ Bracket.σ) w = 0 :=
  comp_sigma_flat_general hk hw0 (((hsm j).contDiffAt (Metric.isOpen_ball.mem_nhds hwin)).of_le two_le_infty)
    (flat_of_isJacobiField (k := k) hk hjac j hwin)

theorem reflected_flat_jacobi {m : ℕ} {u : ZMod (2 * m) → ℂ → ℂ}
    (hsm : ∀ n, ContDiffOn ℝ ∞ (u n) disk) (hjac : IsJacobiField 3 m u)
    (j : ZMod (2 * m)) {w : ℂ} (hw0 : w ≠ 0) (hwin : Bracket.σ w ∈ disk) :
    laplacian (u j ∘ Bracket.σ) w + (potV 3 w : ℂ) * (u j ∘ Bracket.σ) w = 0 := by
  exact reflected_flat_jacobi_general (by norm_num : 2 ≤ 3) hsm hjac j hw0 hwin

/-- **The reflected end-chart Jacobi equation.**  Where `σ_c(ζ)` lands strictly
outside the disk (`σ(σ_c ζ)` inside), the reflected copy `u j ∘ σ ∘ σ_c` solves the
transformed equation with the same `generalEndPotential k p m` coefficient as the interior branch. -/
theorem endComp_reflected_general {k m : ℕ} (hk : 2 ≤ k) {u : ZMod (2 * m) → ℂ → ℂ}
    (hsm : ∀ n, ContDiffOn ℝ ∞ (u n) disk) (hjac : IsJacobiField k m u)
    (p : ℂ) (j : ZMod (2 * m)) {ζ : ℂ}
    (hne : endChart p m ζ ≠ 0) (hout : Bracket.σ (endChart p m ζ) ∈ disk) :
    laplacian (fun z => u j (Bracket.σ (endChart p m z))) ζ
      + (generalEndPotential k p m ζ : ℂ) * u j (Bracket.σ (endChart p m ζ)) = 0 := by
  have hσC2 : ContDiffAt ℝ 2 Bracket.σ (endChart p m ζ) :=
    (Bracket.contDiffAt_σ hne).of_le two_le_infty
  have huC2 : ContDiffAt ℝ 2 (u j) (Bracket.σ (endChart p m ζ)) :=
    ((hsm j).contDiffAt (Metric.isOpen_ball.mem_nhds hout)).of_le two_le_infty
  have hC2 : ContDiffAt ℝ 2 (u j ∘ Bracket.σ) (endChart p m ζ) :=
    huC2.comp (endChart p m ζ) hσC2
  exact endComp_of_flat_general k p hC2 (reflected_flat_jacobi_general hk hsm hjac j hne hout)

theorem endComp_reflected {m : ℕ} {u : ZMod (2 * m) → ℂ → ℂ}
    (hsm : ∀ n, ContDiffOn ℝ ∞ (u n) disk) (hjac : IsJacobiField 3 m u)
    (p : ℂ) (j : ZMod (2 * m)) {ζ : ℂ}
    (hne : endChart p m ζ ≠ 0) (hout : Bracket.σ (endChart p m ζ) ∈ disk) :
    laplacian (fun z => u j (Bracket.σ (endChart p m z))) ζ
      + (endPotential p m ζ : ℂ) * u j (Bracket.σ (endChart p m ζ)) = 0 := by
  simpa only [generalEndPotential_three] using
    endComp_reflected_general (by norm_num : 2 ≤ 3) hsm hjac p j hne hout

/-! ### The flat equation at seam points

At a point of `seamArc k m n`, the `IsSmooth` germ makes the flat-equation
residual continuous. It vanishes in the open disk, and the seam point lies
in the closure of that disk, so the residual vanishes there as well. -/

/-- Two functions agreeing on a neighborhood have the same flat Laplacian there. -/
lemma laplacian_congr_of_eventuallyEq {f g : ℂ → ℂ} {w : ℂ} (h : f =ᶠ[nhds w] g) :
    laplacian f w = laplacian g w := by
  have hfd : ∀ᶠ z in nhds w, fderiv ℝ f z = fderiv ℝ g z := by
    obtain ⟨U, hUsub, hUopen, hwU⟩ := mem_nhds_iff.mp h
    filter_upwards [hUopen.mem_nhds hwU] with z hz
    exact (Filter.eventuallyEq_of_mem (hUopen.mem_nhds hz) hUsub).fderiv_eq
  have e1 : (fun z => fderiv ℝ f z 1) =ᶠ[nhds w] (fun z => fderiv ℝ g z 1) := by
    filter_upwards [hfd] with z hz; rw [hz]
  have eI : (fun z => fderiv ℝ f z Complex.I) =ᶠ[nhds w] (fun z => fderiv ℝ g z Complex.I) := by
    filter_upwards [hfd] with z hz; rw [hz]
  unfold laplacian
  rw [e1.fderiv_eq, eI.fderiv_eq]

/-- The flat Laplacian of a `C²` field is continuous at the point. -/
lemma continuousAt_laplacian {f : ℂ → ℂ} {w₀ : ℂ} (hf : ContDiffAt ℝ 2 f w₀) :
    ContinuousAt (laplacian f) w₀ := by
  have key : ∀ v : ℂ, ContinuousAt (fun w => fderiv ℝ (fun z => fderiv ℝ f z v) w v) w₀ := by
    intro v
    have hD1 : ContDiffAt ℝ 1 (fderiv ℝ f) w₀ := hf.fderiv_right (m := 1) (by norm_num)
    have hD1v : ContDiffAt ℝ 1 (fun z => fderiv ℝ f z v) w₀ :=
      (ContinuousLinearMap.apply ℝ ℂ v).contDiff.contDiffAt.comp w₀ hD1
    have hfd : ContinuousAt (fderiv ℝ (fun z => fderiv ℝ f z v)) w₀ :=
      (hD1v.fderiv_right (m := 0) (by norm_num)).continuousAt
    exact hfd.clm_apply continuousAt_const
  unfold laplacian
  exact (key 1).add (key I)

/-- **Seam value of the flat equation.**  `glue u n` solves `Δ + potV k·(·) = 0` at every
nonzero point of `seamArc n`. -/
theorem glue_flat_jacobi_general {k m : ℕ} (hk : 2 ≤ k) {u : ZMod (2 * m) → ℂ → ℂ}
    (hsmooth : IsSmooth k m u) (hjac : IsJacobiField k m u) (n : ZMod (2 * m))
    {w₀ : ℂ} (hw₀ : w₀ ∈ seamArc k m n) :
    laplacian (glue u n) w₀ + (potV k w₀ : ℂ) * glue u n w₀ = 0 := by
  set G : ℂ → ℂ := fun w => laplacian (glue u n) w + (potV k w : ℂ) * glue u n w with hG
  have hgerm : ContDiffAt ℝ 2 (glue u n) w₀ := (hsmooth.2.1 n w₀ hw₀).of_le two_le_infty
  -- G is continuous at w₀
  have hpotc : ContinuousAt (fun w => (potV k w : ℂ)) w₀ := by
    refine (Complex.continuous_ofReal.comp ?_).continuousAt
    unfold potV
    exact (continuous_const.mul (continuous_norm.pow _)).div
      (((continuous_norm.pow _).add continuous_const).pow 2) (fun w => by positivity)
  have hGcont : ContinuousAt G w₀ :=
    (continuousAt_laplacian hgerm).add (hpotc.mul hgerm.continuousAt)
  -- G vanishes on the open disk
  have hG0 : ∀ w ∈ disk, G w = 0 := by
    intro w hw
    have hwlt : ‖w‖ < 1 := by rw [disk, Metric.mem_ball, dist_zero_right] at hw; exact hw
    have hglue : glue u n =ᶠ[nhds w] u n := by
      filter_upwards [Metric.isOpen_ball.mem_nhds (show w ∈ Metric.ball 0 1 from by
        rw [Metric.mem_ball, dist_zero_right]; exact hwlt)] with w' hw'
      have : ‖w'‖ ≤ 1 := le_of_lt (by rwa [Metric.mem_ball, dist_zero_right] at hw')
      simp only [glue, if_pos this]
    simp only [hG, laplacian_congr_of_eventuallyEq hglue, hglue.self_of_nhds]
    exact flat_of_isJacobiField hk hjac n hw
  -- w₀ is in the closure of the disk; conclude by continuity
  have hcl : w₀ ∈ closure disk := by
    rw [disk, closure_ball (0 : ℂ) one_ne_zero, Metric.mem_closedBall, dist_zero_right]
    exact le_of_eq hw₀.1
  haveI : (nhdsWithin w₀ disk).NeBot := mem_closure_iff_nhdsWithin_neBot.mp hcl
  have htend1 : Filter.Tendsto G (nhdsWithin w₀ disk) (nhds (G w₀)) := hGcont.continuousWithinAt
  have htend0 : Filter.Tendsto G (nhdsWithin w₀ disk) (nhds 0) := by
    have heq : G =ᶠ[nhdsWithin w₀ disk] fun _ => (0 : ℂ) := by
      filter_upwards [self_mem_nhdsWithin] with w hw using hG0 w hw
    exact (tendsto_congr' heq).mpr tendsto_const_nhds
  exact tendsto_nhds_unique htend1 htend0

theorem glue_flat_jacobi {m : ℕ} {u : ZMod (2 * m) → ℂ → ℂ}
    (hsmooth : IsSmooth 3 m u) (hjac : IsJacobiField 3 m u) (n : ZMod (2 * m))
    {w₀ : ℂ} (hw₀ : w₀ ∈ seamArc 3 m n) :
    laplacian (glue u n) w₀ + (potV 3 w₀ : ℂ) * glue u n w₀ = 0 := by
  exact glue_flat_jacobi_general (by norm_num : 2 ≤ 3) hsmooth hjac n hw₀

/-- **Flat equation on the interior.**  `glue u n` reads copy `u n` on the open disk, so it
solves `Δ + potV k·(·) = 0` there directly. -/
theorem glue_flat_disk_general {k m : ℕ} (hk : 2 ≤ k) {u : ZMod (2 * m) → ℂ → ℂ} (hjac : IsJacobiField k m u)
    (n : ZMod (2 * m)) {w₀ : ℂ} (hw : ‖w₀‖ < 1) :
    laplacian (glue u n) w₀ + (potV k w₀ : ℂ) * glue u n w₀ = 0 := by
  have hmem : w₀ ∈ disk := by rw [disk, Metric.mem_ball, dist_zero_right]; exact hw
  have hglue : glue u n =ᶠ[nhds w₀] u n := by
    filter_upwards [Metric.isOpen_ball.mem_nhds (show w₀ ∈ Metric.ball (0 : ℂ) 1 from
      by rw [Metric.mem_ball, dist_zero_right]; exact hw)] with w' hw'
    have hle : ‖w'‖ ≤ 1 := le_of_lt (by rwa [Metric.mem_ball, dist_zero_right] at hw')
    simp only [glue, if_pos hle]
  rw [laplacian_congr_of_eventuallyEq hglue, hglue.self_of_nhds]
  exact flat_of_isJacobiField hk hjac n hmem

theorem glue_flat_disk {m : ℕ} {u : ZMod (2 * m) → ℂ → ℂ} (hjac : IsJacobiField 3 m u)
    (n : ZMod (2 * m)) {w₀ : ℂ} (hw : ‖w₀‖ < 1) :
    laplacian (glue u n) w₀ + (potV 3 w₀ : ℂ) * glue u n w₀ = 0 := by
  exact glue_flat_disk_general (by norm_num : 2 ≤ 3) hjac n hw

/-- **Flat equation on the exterior.**  `glue u n` reads the reflected copy `u(n+1)∘σ` outside
the disk, which solves `Δ + potV k·(·) = 0` by `reflected_flat_jacobi`. -/
theorem glue_flat_exterior_general {k m : ℕ} (hk : 2 ≤ k) {u : ZMod (2 * m) → ℂ → ℂ}
    (hsm : ∀ n, ContDiffOn ℝ ∞ (u n) disk) (hjac : IsJacobiField k m u)
    (n : ZMod (2 * m)) {w₀ : ℂ} (hw : 1 < ‖w₀‖) :
    laplacian (glue u n) w₀ + (potV k w₀ : ℂ) * glue u n w₀ = 0 := by
  have hw0 : w₀ ≠ 0 := fun h => by rw [h, norm_zero] at hw; linarith
  have hσin : Bracket.σ w₀ ∈ disk := by
    rw [disk, Metric.mem_ball, dist_zero_right, Bracket.norm_σ]
    exact (inv_lt_one₀ (by linarith)).mpr hw
  have hglue : glue u n =ᶠ[nhds w₀] (u (n + 1) ∘ Bracket.σ) := by
    filter_upwards [(isOpen_lt continuous_const continuous_norm).mem_nhds hw] with w' hw'
    simp only [glue, if_neg (not_le.mpr hw'), Function.comp_apply, Bracket.σ_apply]
  rw [laplacian_congr_of_eventuallyEq hglue, show glue u n w₀ = (u (n + 1) ∘ Bracket.σ) w₀ from
    hglue.self_of_nhds]
  exact reflected_flat_jacobi_general hk hsm hjac (n + 1) hw0 hσin

theorem glue_flat_exterior {m : ℕ} {u : ZMod (2 * m) → ℂ → ℂ}
    (hsm : ∀ n, ContDiffOn ℝ ∞ (u n) disk) (hjac : IsJacobiField 3 m u)
    (n : ZMod (2 * m)) {w₀ : ℂ} (hw : 1 < ‖w₀‖) :
    laplacian (glue u n) w₀ + (potV 3 w₀ : ℂ) * glue u n w₀ = 0 := by
  exact glue_flat_exterior_general (by norm_num : 2 ≤ 3) hsm hjac n hw

/-! ### Local `C²` regularity of `glue u n` in the disk and exterior -/

/-- `glue u n` is `C²` on the open disk (where it reads `u n`). -/
lemma glue_contDiffAt_disk {m : ℕ} {u : ZMod (2 * m) → ℂ → ℂ}
    (hsm : ∀ n, ContDiffOn ℝ ∞ (u n) disk) (n : ZMod (2 * m)) {w₀ : ℂ} (hw : ‖w₀‖ < 1) :
    ContDiffAt ℝ 2 (glue u n) w₀ := by
  have hball : w₀ ∈ Metric.ball (0 : ℂ) 1 := by rw [Metric.mem_ball, dist_zero_right]; exact hw
  have hglue : glue u n =ᶠ[nhds w₀] u n := by
    filter_upwards [Metric.isOpen_ball.mem_nhds hball] with w' hw'
    have hle : ‖w'‖ ≤ 1 := le_of_lt (by rwa [Metric.mem_ball, dist_zero_right] at hw')
    simp only [glue, if_pos hle]
  exact (((hsm n).contDiffAt (Metric.isOpen_ball.mem_nhds hball)).of_le
    two_le_infty).congr_of_eventuallyEq hglue

/-- `glue u n` is `C²` outside the closed disk (where it reads the reflected copy `u(n+1)∘σ`). -/
lemma glue_contDiffAt_exterior {m : ℕ} {u : ZMod (2 * m) → ℂ → ℂ}
    (hsm : ∀ n, ContDiffOn ℝ ∞ (u n) disk) (n : ZMod (2 * m)) {w₀ : ℂ} (hw : 1 < ‖w₀‖) :
    ContDiffAt ℝ 2 (glue u n) w₀ := by
  have hw0 : w₀ ≠ 0 := fun h => by rw [h, norm_zero] at hw; linarith
  have hσin : Bracket.σ w₀ ∈ disk := by
    rw [disk, Metric.mem_ball, dist_zero_right, Bracket.norm_σ]
    exact (inv_lt_one₀ (by linarith)).mpr hw
  have hglue : glue u n =ᶠ[nhds w₀] (u (n + 1) ∘ Bracket.σ) := by
    filter_upwards [(isOpen_lt continuous_const continuous_norm).mem_nhds hw] with w' hw'
    simp only [glue, if_neg (not_le.mpr hw'), Function.comp_apply, Bracket.σ_apply]
  have hcu : ContDiffAt ℝ 2 (u (n + 1) ∘ Bracket.σ) w₀ :=
    (((hsm (n + 1)).contDiffAt (Metric.isOpen_ball.mem_nhds hσin)).of_le two_le_infty).comp w₀
      ((Bracket.contDiffAt_σ hw0).of_le two_le_infty)
  exact hcu.congr_of_eventuallyEq hglue

end KsIndex.EndChart
