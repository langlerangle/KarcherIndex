module

/-
# Disk-chain function spaces and Jacobi forms

The coordinate model uses `2m` copies of the closed unit disk minus the punctures
`P_k = {w | w^(2k) = -1}`, indexed by `ZMod (2m)`. Adjacent copies meet along
alternating arc families. Across the seam from copy `n` to `n+1`, the chart uses
`w` on the first copy and `1/w̄` on the second. These coordinates and the conformal
metric formulas come from the Enneper–Weierstrass description in [ksindexi].
Geometric identifications and transport of index and nullity are separate results
in the library; this file defines the coordinate spaces and forms they use.

Representatives are families `u : ZMod (2m) → ℂ → ℂ`. `IsSmooth` requires smoothness
on each open disk and of the glued function at every seam point, together with
zero extension outside the closed disk. `CcSmooth` adds vanishing near the deleted
punctures. These are the predicates used for the coordinate index domain; zero
extension alone does not assert a bijection with functions on the glued surface.

`BoundedJacobi` adds boundedness and the Jacobi equation on each open disk. It also
requires `PunctureZero`, assigning zero at deleted punctures, and `SeamVal`, matching
the two representatives at each seam point. The theorem `boundedJacobi_ext` proves
uniqueness of these representatives from their values on the punctured disk chain.

`indSurface` is the index of `jacobiQ` on `CcSmooth`, and `nulSurface` is the complex
dimension of `BoundedJacobi`, with values in `ℕ∞`. The Jacobi form retains the metric
factor `rho` and curvature factor `absA`. For `k ≥ 2`, the conformal-collapse lemmas
identify each disk contribution with the flat Dirichlet integral minus the
potential integral, where
`V_k = 8(k−1)^2 |w|^(2k−4) / (|w|^(2k−2)+1)^2`.
-/
public import Mathlib
public import KsIndexLean.FormIndex

@[expose] public section


noncomputable section

open Complex Real
open scoped ContDiff

namespace KsIndex.Surface

/-! ### Karcher's data (`ewcover`) -/

/-- The puncture set `P_k = {w : w^{2k} = −1}` — the ends of `Ξ_k` in the chart. -/
def punctures (k : ℕ) : Set ℂ := {w | w ^ (2 * k) = -1}

/-- The arc family `arcs_{k,n} = {θ : (−1)^n cos kθ < 0}`, on the unit circle in `ℂ`
(`cos kθ = Re(w^k)` for `|w| = 1`). -/
def arc (k n : ℕ) : Set ℂ := {w | ‖w‖ = 1 ∧ (-1 : ℝ) ^ n * (w ^ k).re < 0}

/-- The open unit disk: the interior of a half period. -/
def disk : Set ℂ := Metric.ball 0 1

/-- The conformal factor `ρ_k = k(|w|^{2k−2}+1)/|w^{2k}+1|` (`ewcover` (vi)). -/
def rho (k : ℕ) (w : ℂ) : ℝ := k * (‖w‖ ^ (2 * k - 2) + 1) / ‖w ^ (2 * k) + 1‖

/-- `|A_k|_{g_k} = 2√2 (k−1)/ρ_k · |w|^{k−2}/(|w|^{2k−2}+1)` (`ewcover` (vi)). -/
def absA (k : ℕ) (w : ℂ) : ℝ :=
  2 * Real.sqrt 2 * ((k : ℝ) - 1) / rho k w * (‖w‖ ^ (k - 2) / (‖w‖ ^ (2 * k - 2) + 1))

/-- The flat-chart Jacobi potential `V_k = ρ_k²|A_k|² = 8(k−1)²|w|^{2k−4}/(|w|^{2k−2}+1)²`. -/
def potV (k : ℕ) (w : ℂ) : ℝ :=
  8 * ((k : ℝ) - 1) ^ 2 * ‖w‖ ^ (2 * k - 4) / (‖w‖ ^ (2 * k - 2) + 1) ^ 2

/-! ### The disk chain: copies, seams, functions -/

/-- The parity of a copy index: `ZMod (2m) → ZMod 2`. -/
def parity (m : ℕ) : ZMod (2 * m) →+* ZMod 2 := ZMod.castHom (dvd_mul_right 2 m) (ZMod 2)

/-- The seam between copies `n` and `n+1` is along `arcs_{k,(n+1) mod 2}`. -/
def seamArc (k m : ℕ) (n : ZMod (2 * m)) : Set ℂ := arc k (parity m (n + 1)).val

/-- The glued function across the seam `(n, n+1)`: copy `n` on the closed disk, copy `n+1`
reflected through the unit circle (`w ↦ 1/w̄`). -/
def glue {m : ℕ} (u : ZMod (2 * m) → ℂ → ℂ) (n : ZMod (2 * m)) (w : ℂ) : ℂ :=
  if ‖w‖ ≤ 1 then u n w else u (n + 1) (1 / (starRingEnd ℂ) w)

/-- Smoothness of the disk restrictions and glued seam functions, with zero extension
outside the closed disk. Puncture normalization and receiving seam values are separate predicates. -/
def IsSmooth (k m : ℕ) (u : ZMod (2 * m) → ℂ → ℂ) : Prop :=
  (∀ n, ContDiffOn ℝ ∞ (u n) disk)
    ∧ (∀ n, ∀ w ∈ seamArc k m n, ContDiffAt ℝ ∞ (glue u n) w)
    ∧ (∀ n w, 1 < ‖w‖ → u n w = 0)

/-- Vanishing on a neighbourhood of the punctures (compact support on `Ξ_{k,m}`). -/
def SuppAwayP (k m : ℕ) (u : ZMod (2 * m) → ℂ → ℂ) : Prop :=
  ∃ ε > 0, ∀ n w, (∃ p ∈ punctures k, ‖w - p‖ < ε) → u n w = 0

/-- Boundedness on `Ξ_{k,m}`. -/
def IsBounded {m : ℕ} (u : ZMod (2 * m) → ℂ → ℂ) : Prop := ∃ C : ℝ, ∀ n w, ‖u n w‖ ≤ C

/-! ### The Jacobi form -/

/-- `|∇f|² = ‖∂_x f‖² + ‖∂_y f‖²` (flat gradient of a `ℂ`-valued function on `ℂ ≅ ℝ²`). -/
def gradSq (f : ℂ → ℂ) (w : ℂ) : ℝ := ‖fderiv ℝ f w 1‖ ^ 2 + ‖fderiv ℝ f w I‖ ^ 2

/-- `‖∇_g f‖²_{L²(g)}` on one half period, `g = ρ_k²|dw|²`:
`|∇_g f|²_g = ρ^{−2}|∇f|²`, `dA_g = ρ² dA`. -/
def dirichletG (k : ℕ) (f : ℂ → ℂ) : ℝ :=
  ∫ w in disk, (gradSq f w / rho k w ^ 2) * rho k w ^ 2

/-- `‖|A_k| f‖²_{L²(g)}` on one half period. -/
def potentialG (k : ℕ) (f : ℂ → ℂ) : ℝ :=
  ∫ w in disk, (absA k w * ‖f w‖) ^ 2 * rho k w ^ 2

/-- The Jacobi quadratic form `‖∇_g u‖²_{L²(g)} − ‖|A|u‖²_{L²(g)}` on `Ξ_{k,m}`: the sum over the
`2m` half periods. -/
def jacobiQ (k m : ℕ) [NeZero m] (u : ZMod (2 * m) → ℂ → ℂ) : ℝ :=
  haveI : NeZero (2 * m) := ⟨by have := NeZero.ne m; omega⟩
  ∑ n : ZMod (2 * m), (dirichletG k (u n) - potentialG k (u n))

/-- The flat Laplacian `∂_x² + ∂_y²` of a `ℂ`-valued function on `ℂ`. -/
def laplacian (f : ℂ → ℂ) (w : ℂ) : ℂ :=
  fderiv ℝ (fun z => fderiv ℝ f z 1) w 1 + fderiv ℝ (fun z => fderiv ℝ f z I) w I

/-- `Δ_g = ρ_k^{−2} Δ` for `g = ρ_k²|dw|²`. -/
def laplacianG (k : ℕ) (f : ℂ → ℂ) (w : ℂ) : ℂ := ((rho k w ^ 2)⁻¹ : ℝ) * laplacian f w

/-- The Jacobi equation `Δ_g u + |A_k|² u = 0` on every half period. -/
def IsJacobiField (k m : ℕ) (u : ZMod (2 * m) → ℂ → ℂ) : Prop :=
  ∀ n, ∀ w ∈ disk, laplacianG k (u n) w + ((absA k w ^ 2 : ℝ) : ℂ) * u n w = 0

/-! ### Closure under the vector-space operations -/

lemma glue_add {m : ℕ} (u v : ZMod (2 * m) → ℂ → ℂ) (n : ZMod (2 * m)) :
    glue (u + v) n = glue u n + glue v n := by
  funext w
  simp only [glue, Pi.add_apply]
  split_ifs <;> rfl

lemma glue_smul {m : ℕ} (c : ℂ) (u : ZMod (2 * m) → ℂ → ℂ) (n : ZMod (2 * m)) :
    glue (c • u) n = c • glue u n := by
  funext w
  simp only [glue, Pi.smul_apply]
  split_ifs <;> rfl

lemma glue_zero {m : ℕ} (n : ZMod (2 * m)) : glue (0 : ZMod (2 * m) → ℂ → ℂ) n = 0 := by
  funext w
  simp only [glue, Pi.zero_apply]
  split_ifs <;> rfl

lemma isSmooth_zero (k m : ℕ) : IsSmooth k m 0 := by
  refine ⟨fun n => contDiffOn_const, fun n w _ => ?_, fun n w _ => rfl⟩
  rw [glue_zero]
  exact contDiffAt_const

lemma isSmooth_add {k m : ℕ} {u v : ZMod (2 * m) → ℂ → ℂ} (hu : IsSmooth k m u)
    (hv : IsSmooth k m v) : IsSmooth k m (u + v) := by
  refine ⟨fun n => (hu.1 n).add (hv.1 n), fun n w hw => ?_, fun n w hw => ?_⟩
  · rw [glue_add]
    exact (hu.2.1 n w hw).add (hv.2.1 n w hw)
  · simp only [Pi.add_apply, hu.2.2 n w hw, hv.2.2 n w hw, add_zero]

lemma isSmooth_smul {k m : ℕ} (c : ℂ) {u : ZMod (2 * m) → ℂ → ℂ} (hu : IsSmooth k m u) :
    IsSmooth k m (c • u) := by
  refine ⟨fun n => (hu.1 n).const_smul c, fun n w hw => ?_, fun n w hw => ?_⟩
  · rw [glue_smul]
    exact (hu.2.1 n w hw).const_smul c
  · simp only [Pi.smul_apply, hu.2.2 n w hw, smul_zero]

lemma suppAwayP_zero (k m : ℕ) : SuppAwayP k m 0 := ⟨1, one_pos, fun _ _ _ => rfl⟩

lemma suppAwayP_add {k m : ℕ} {u v : ZMod (2 * m) → ℂ → ℂ} (hu : SuppAwayP k m u)
    (hv : SuppAwayP k m v) : SuppAwayP k m (u + v) := by
  obtain ⟨ε₁, h₁, hu⟩ := hu
  obtain ⟨ε₂, h₂, hv⟩ := hv
  refine ⟨min ε₁ ε₂, lt_min h₁ h₂, fun n w hw => ?_⟩
  obtain ⟨p, hp, hwp⟩ := hw
  simp only [Pi.add_apply]
  rw [hu n w ⟨p, hp, lt_of_lt_of_le hwp (min_le_left _ _)⟩,
    hv n w ⟨p, hp, lt_of_lt_of_le hwp (min_le_right _ _)⟩, add_zero]

lemma suppAwayP_smul {k m : ℕ} (c : ℂ) {u : ZMod (2 * m) → ℂ → ℂ} (hu : SuppAwayP k m u) :
    SuppAwayP k m (c • u) := by
  obtain ⟨ε, hε, hu⟩ := hu
  exact ⟨ε, hε, fun n w hw => by simp only [Pi.smul_apply, hu n w hw, smul_zero]⟩

lemma isBounded_zero {m : ℕ} : IsBounded (0 : ZMod (2 * m) → ℂ → ℂ) :=
  ⟨0, fun _ _ => by simp⟩

lemma isBounded_add {m : ℕ} {u v : ZMod (2 * m) → ℂ → ℂ} (hu : IsBounded u)
    (hv : IsBounded v) : IsBounded (u + v) := by
  obtain ⟨C, hu⟩ := hu
  obtain ⟨D, hv⟩ := hv
  exact ⟨C + D, fun n w => by
    simp only [Pi.add_apply]
    exact le_trans (norm_add_le _ _) (add_le_add (hu n w) (hv n w))⟩

lemma isBounded_smul {m : ℕ} (c : ℂ) {u : ZMod (2 * m) → ℂ → ℂ} (hu : IsBounded u) :
    IsBounded (c • u) := by
  obtain ⟨C, hu⟩ := hu
  exact ⟨‖c‖ * C, fun n w => by
    simp only [Pi.smul_apply, smul_eq_mul, norm_mul]
    exact mul_le_mul_of_nonneg_left (hu n w) (norm_nonneg c)⟩

lemma isJacobiField_zero (k m : ℕ) : IsJacobiField k m 0 := by
  intro n w _
  simp [laplacianG, laplacian]


lemma two_le_infty : (2 : WithTop ℕ∞) ≤ ∞ := by
  simpa using (WithTop.coe_le_coe.mpr (le_top : (2 : ℕ∞) ≤ ⊤))

/-- Additivity of the flat Laplacian at a point of `C^∞`-smoothness. -/
lemma laplacian_add {f g : ℂ → ℂ} {w : ℂ} (hf : ContDiffAt ℝ ∞ f w) (hg : ContDiffAt ℝ ∞ g w) :
    laplacian (f + g) w = laplacian f w + laplacian g w := by
  have hf2 : ContDiffAt ℝ 2 f w := hf.of_le two_le_infty
  have hg2 : ContDiffAt ℝ 2 g w := hg.of_le two_le_infty
  have h1 : ∀ v : ℂ, (fun z => fderiv ℝ (f + g) z v)
      =ᶠ[nhds w] (fun z => fderiv ℝ f z v) + (fun z => fderiv ℝ g z v) := by
    intro v
    filter_upwards [hf2.eventually (by simp), hg2.eventually (by simp)] with z hfz hgz
    rw [fderiv_add (hfz.differentiableAt (by norm_num)) (hgz.differentiableAt (by norm_num))]
    rfl
  have hdf : ∀ v : ℂ, DifferentiableAt ℝ (fun z => fderiv ℝ f z v) w := fun v =>
    ((hf.fderiv_right (m := 1)
      (by simpa using (WithTop.coe_le_coe.mpr (le_top : (1 + 1 : ℕ∞) ≤ ⊤)))).clm_apply
        contDiffAt_const).differentiableAt one_ne_zero
  have hdg : ∀ v : ℂ, DifferentiableAt ℝ (fun z => fderiv ℝ g z v) w := fun v =>
    ((hg.fderiv_right (m := 1)
      (by simpa using (WithTop.coe_le_coe.mpr (le_top : (1 + 1 : ℕ∞) ≤ ⊤)))).clm_apply
        contDiffAt_const).differentiableAt one_ne_zero
  simp only [laplacian]
  rw [(h1 1).fderiv_eq, (h1 I).fderiv_eq, fderiv_add (hdf 1) (hdg 1), fderiv_add (hdf I) (hdg I)]
  simp only [add_apply]
  ring

/-- Homogeneity of the flat Laplacian at a point of `C^∞`-smoothness. -/
lemma laplacian_smul (c : ℂ) {f : ℂ → ℂ} {w : ℂ} (hf : ContDiffAt ℝ ∞ f w) :
    laplacian (c • f) w = c * laplacian f w := by
  have hf2 : ContDiffAt ℝ 2 f w := hf.of_le two_le_infty
  have h1 : ∀ v : ℂ, (fun z => fderiv ℝ (c • f) z v)
      =ᶠ[nhds w] fun z => c * fderiv ℝ f z v := by
    intro v
    filter_upwards [hf2.eventually (by simp)] with z hfz
    rw [fderiv_const_smul (hfz.differentiableAt (by norm_num))]
    rfl
  have hdf : ∀ v : ℂ, DifferentiableAt ℝ (fun z => fderiv ℝ f z v) w := fun v =>
    ((hf.fderiv_right (m := 1)
      (by simpa using (WithTop.coe_le_coe.mpr (le_top : (1 + 1 : ℕ∞) ≤ ⊤)))).clm_apply
        contDiffAt_const).differentiableAt one_ne_zero
  simp only [laplacian]
  rw [(h1 1).fderiv_eq, (h1 I).fderiv_eq, fderiv_const_mul (hdf 1),
    fderiv_const_mul (hdf I)]
  simp only [FunLike.coe_smul, Pi.smul_apply, smul_eq_mul]
  ring

lemma isJacobiField_add {k m : ℕ} {u v : ZMod (2 * m) → ℂ → ℂ} (hu : IsSmooth k m u)
    (hv : IsSmooth k m v) (hJu : IsJacobiField k m u) (hJv : IsJacobiField k m v) :
    IsJacobiField k m (u + v) := by
  intro n w hw
  have hwo : disk ∈ nhds w := Metric.isOpen_ball.mem_nhds hw
  have hL := laplacian_add ((hu.1 n).contDiffAt hwo) ((hv.1 n).contDiffAt hwo)
  have e1 := hJu n w hw
  have e2 := hJv n w hw
  simp only [laplacianG, Pi.add_apply] at e1 e2 ⊢
  rw [hL]
  linear_combination e1 + e2

lemma isJacobiField_smul {k m : ℕ} (c : ℂ) {u : ZMod (2 * m) → ℂ → ℂ} (hu : IsSmooth k m u)
    (hJu : IsJacobiField k m u) : IsJacobiField k m (c • u) := by
  intro n w hw
  have hwo : disk ∈ nhds w := Metric.isOpen_ball.mem_nhds hw
  have hL := laplacian_smul c ((hu.1 n).contDiffAt hwo)
  have e1 := hJu n w hw
  simp only [laplacianG, Pi.smul_apply, smul_eq_mul] at e1 ⊢
  rw [hL]
  linear_combination c * e1

/-! ### Coordinate function spaces, index and nullity -/

/-- `C_c^∞(Ξ_{k,m})` as a complex subspace of the families `ZMod (2m) → ℂ → ℂ`. -/
def CcSmooth (k m : ℕ) : Submodule ℂ (ZMod (2 * m) → ℂ → ℂ) where
  carrier := {u | IsSmooth k m u ∧ SuppAwayP k m u}
  zero_mem' := ⟨isSmooth_zero k m, suppAwayP_zero k m⟩
  add_mem' := fun hu hv => ⟨isSmooth_add hu.1 hv.1, suppAwayP_add hu.2 hv.2⟩
  smul_mem' := fun c _ hu => ⟨isSmooth_smul c hu.1, suppAwayP_smul c hu.2⟩

/-- Set the representative to zero at every deleted puncture. Punctures are not
surface points, so this assigns otherwise unused coordinate values rather than
imposing a boundary or decay condition. See `PunctureSpike` for a point-supported
function excluded by this normalization. -/
def PunctureZero (k : ℕ) {m : ℕ} (u : ZMod (2 * m) → ℂ → ℂ) : Prop :=
  ∀ n, ∀ p ∈ punctures k, u n p = 0

lemma punctureZero_zero (k m : ℕ) : PunctureZero k (0 : ZMod (2 * m) → ℂ → ℂ) :=
  fun _ _ _ => rfl

lemma punctureZero_add {k m : ℕ} {u v : ZMod (2 * m) → ℂ → ℂ}
    (hu : PunctureZero k u) (hv : PunctureZero k v) : PunctureZero k (u + v) :=
  fun n p hp => by simp only [Pi.add_apply, hu n p hp, hv n p hp, add_zero]

lemma punctureZero_smul {k m : ℕ} (c : ℂ) {u : ZMod (2 * m) → ℂ → ℂ}
    (hu : PunctureZero k u) : PunctureZero k (c • u) :=
  fun n p hp => by simp only [Pi.smul_apply, hu n p hp, smul_zero]

/-- Match the two chart values at every seam point. The inside branch of `glue`
uses copy `n`; this predicate also fixes the value of copy `n+1` at the identified
point. It expresses single-valuedness on the glued surface, not an additional
boundary condition on Jacobi fields. See `ArcSpike` for the point-supported
function excluded by this requirement. -/
def SeamVal (k : ℕ) {m : ℕ} (u : ZMod (2 * m) → ℂ → ℂ) : Prop :=
  ∀ n, ∀ w ∈ seamArc k m n, u (n + 1) w = u n w

lemma seamVal_zero (k m : ℕ) : SeamVal k (0 : ZMod (2 * m) → ℂ → ℂ) := fun _ _ _ => rfl

lemma seamVal_add {k m : ℕ} {u v : ZMod (2 * m) → ℂ → ℂ}
    (hu : SeamVal k u) (hv : SeamVal k v) : SeamVal k (u + v) :=
  fun n w hw => by simp only [Pi.add_apply, hu n w hw, hv n w hw]

lemma seamVal_smul {k m : ℕ} (c : ℂ) {u : ZMod (2 * m) → ℂ → ℂ}
    (hu : SeamVal k u) : SeamVal k (c • u) :=
  fun n w hw => by simp only [Pi.smul_apply, hu n w hw]

/-- The bounded smooth Jacobi fields `{u ∈ C^∞(Ξ_{k,m}) ∩ L^∞ : Δ_g u + |A|² u = 0}`, with the
representative normalized to `0` at the deleted punctures (`PunctureZero`) and single-valued on
the seam arcs (`SeamVal`). -/
def BoundedJacobi (k m : ℕ) : Submodule ℂ (ZMod (2 * m) → ℂ → ℂ) where
  carrier := {u | IsSmooth k m u ∧ IsBounded u ∧ IsJacobiField k m u ∧ PunctureZero k u
    ∧ SeamVal k u}
  zero_mem' := ⟨isSmooth_zero k m, isBounded_zero, isJacobiField_zero k m,
    punctureZero_zero k m, seamVal_zero k m⟩
  add_mem' := fun hu hv => ⟨isSmooth_add hu.1 hv.1, isBounded_add hu.2.1 hv.2.1,
    isJacobiField_add hu.1 hv.1 hu.2.2.1 hv.2.2.1, punctureZero_add hu.2.2.2.1 hv.2.2.2.1,
    seamVal_add hu.2.2.2.2 hv.2.2.2.2⟩
  smul_mem' := fun c _ hu => ⟨isSmooth_smul c hu.1, isBounded_smul c hu.2.1,
    isJacobiField_smul c hu.1 hu.2.2.1, punctureZero_smul c hu.2.2.2.1,
    seamVal_smul c hu.2.2.2.2⟩

/-- The actual domain of the disk chain, per copy: the closed disk minus the punctures. -/
def chainDom (k : ℕ) : Set ℂ := {w : ℂ | ‖w‖ ≤ 1 ∧ w ∉ punctures k}

/-- Two bounded Jacobi representatives agreeing on the punctured disk chain are
equal everywhere. Exterior values are fixed by `IsSmooth`, and deleted-puncture
values by `PunctureZero`. -/
theorem boundedJacobi_ext {k m : ℕ} {u v : ZMod (2 * m) → ℂ → ℂ}
    (hu : u ∈ BoundedJacobi k m) (hv : v ∈ BoundedJacobi k m)
    (h : ∀ n, ∀ w ∈ chainDom k, u n w = v n w) : u = v := by
  funext n w
  by_cases hw1 : 1 < ‖w‖
  · rw [hu.1.2.2 n w hw1, hv.1.2.2 n w hw1]
  · by_cases hwp : w ∈ punctures k
    · rw [hu.2.2.2.1 n w hwp, hv.2.2.2.1 n w hwp]
    · exact h n w ⟨not_lt.mp hw1, hwp⟩

/-- Families `ZMod (2m) → ℂ → ℂ` are the functions on `ZMod (2m) × ℂ` (uncurrying), the index
type the generic `FormIndex` engine works with. -/
def uncurryE (m : ℕ) : (ZMod (2 * m) → ℂ → ℂ) ≃ₗ[ℂ] (ZMod (2 * m) × ℂ → ℂ) where
  toFun u := fun p => u p.1 p.2
  invFun U := fun n w => U (n, w)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl

/-- **`ind(Ξ_{k,m})`** — [ksindexi] §2, verbatim: the supremum of `dim X` over subspaces
`X ≤ C_c^∞(Ξ_{k,m})` on which `‖∇_g u‖²_{L²(g)} < ‖|A_k| u‖²_{L²(g)}` for every `u ≠ 0`
(`formIndex` of the Jacobi form on `C_c^∞`, transported along the uncurrying identification). -/
def indSurface (k m : ℕ) [NeZero m] : ℕ∞ :=
  KsIndex.FormIndex.formIndex (fun U => jacobiQ k m ((uncurryE m).symm U))
    ((CcSmooth k m).map (uncurryE m).toLinearMap)

/-- **`nul(Ξ_{k,m})`** — [ksindexi] §2, verbatim: the dimension of the space of bounded smooth
Jacobi fields. -/
def nulSurface (k m : ℕ) : ℕ∞ := Cardinal.toENat (Module.rank ℂ ↥(BoundedJacobi k m))

/-! ### The conformal collapse (the flat form) -/

/-- `ρ_k > 0` away from the punctures. -/
lemma rho_pos {k : ℕ} (hk : 1 ≤ k) {w : ℂ} (hw : w ∉ punctures k) : 0 < rho k w := by
  have hne : w ^ (2 * k) + 1 ≠ 0 := by
    intro h
    exact hw (by simp only [punctures, Set.mem_ofPred_eq]; linear_combination h)
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  unfold rho
  apply div_pos (mul_pos hk' (by positivity))
  exact norm_pos_iff.mpr hne

/-- The Dirichlet integrand collapses to `|∇f|²` off the punctures. -/
lemma dirichlet_integrand {k : ℕ} (hk : 1 ≤ k) (f : ℂ → ℂ) {w : ℂ} (hw : w ∉ punctures k) :
    (gradSq f w / rho k w ^ 2) * rho k w ^ 2 = gradSq f w := by
  have := rho_pos hk hw
  field_simp

/-- The potential integrand collapses to `V_k|f|²` off the punctures. -/
lemma potential_integrand {k : ℕ} (hk : 2 ≤ k) (f : ℂ → ℂ) {w : ℂ} (hw : w ∉ punctures k) :
    (absA k w * ‖f w‖) ^ 2 * rho k w ^ 2 = potV k w * ‖f w‖ ^ 2 := by
  have hρ := rho_pos (by omega) hw
  unfold absA potV
  have hs : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have e : ‖w‖ ^ (2 * k - 4) = (‖w‖ ^ (k - 2)) ^ 2 := by
    rw [← pow_mul]; congr 1; omega
  rw [e]
  field_simp
  rw [hs]
  ring

/-! ### Conformal collapse on the disk (the metric factor cancels) -/

/-- The punctures `P_k = {w^{2k} = −1}` all lie on the unit circle (`‖w^{2k}‖ = 1`), hence off the
OPEN disk.  So on `disk` the collapse lemmas apply pointwise everywhere, not merely a.e. -/
lemma punctures_notMem_disk {k : ℕ} (hk : 1 ≤ k) {w : ℂ} (hw : w ∈ disk) :
    w ∉ punctures k := by
  intro hp
  simp only [punctures, Set.mem_ofPred_eq] at hp
  have hlt : ‖w‖ < 1 := by
    rw [disk, Metric.mem_ball, dist_zero_right] at hw; exact hw
  have h1 : ‖w‖ ^ (2 * k) = 1 := by rw [← norm_pow, hp]; simp
  have h2 : ‖w‖ ^ (2 * k) < 1 := pow_lt_one₀ (norm_nonneg w) hlt (by omega)
  linarith

/-- **Conformal collapse (Dirichlet).**  On the open disk the metric factor `ρ_k²` cancels, so the
geometric Dirichlet energy `‖∇_g f‖²_{L²(g)}` equals the flat Dirichlet energy `∫_D |∇f|²`. -/
lemma dirichletG_collapse {k : ℕ} (hk : 1 ≤ k) (f : ℂ → ℂ) :
    dirichletG k f = ∫ w in disk, gradSq f w := by
  have hmeas : MeasurableSet disk := by rw [disk]; exact measurableSet_ball
  unfold dirichletG
  refine MeasureTheory.setIntegral_congr_fun hmeas (fun w hw => ?_)
  exact dirichlet_integrand hk f (punctures_notMem_disk hk hw)

/-- **Conformal collapse (potential).**  On the open disk `ρ_k²|A_k|² = V_k`, so the geometric
potential term `‖|A_k| f‖²_{L²(g)}` equals the flat potential `∫_D V_k|f|²`. -/
lemma potentialG_collapse {k : ℕ} (hk : 2 ≤ k) (f : ℂ → ℂ) :
    potentialG k f = ∫ w in disk, potV k w * ‖f w‖ ^ 2 := by
  have hmeas : MeasurableSet disk := by rw [disk]; exact measurableSet_ball
  unfold potentialG
  refine MeasureTheory.setIntegral_congr_fun hmeas (fun w hw => ?_)
  exact potential_integrand hk f (punctures_notMem_disk (by omega) hw)

/-- **Conformal collapse of the Jacobi summand.**  Each half-period contribution to `jacobiQ`,
`dirichletG − potentialG`, equals the difference of the two flat integrals over the disk. -/
lemma dirichletG_sub_potentialG {k : ℕ} (hk : 2 ≤ k) (f : ℂ → ℂ) :
    dirichletG k f - potentialG k f
      = (∫ w in disk, gradSq f w) - ∫ w in disk, potV k w * ‖f w‖ ^ 2 := by
  rw [dirichletG_collapse (by omega) f, potentialG_collapse hk f]

end KsIndex.Surface
