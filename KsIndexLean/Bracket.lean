module

/-
KsIndexLean — Bracket: the Dirichlet / quasi-periodic / Neumann bracketing of the one-period
index, and the copy-swap (equator reflection) splitting of the Dirichlet and Neumann problems
(paper `k=3_bracket`, index half).

The one-period surface `Ξ_k^{[0,2π]}` is two disks glued along `arcs_{k,1}` (the seam `(0,1)`);
the second seam `(1,0)`, along `arcs_{k,0}`, is the SLIT of the paper's slit sphere `S²₃`.
Three test spaces on the pairs `v : ZMod 2 → ℂ → ℂ`, all with the same Jacobi form `jacobiQ k 1`:

* `DCc k`  — Dirichlet: vanishing on a neighbourhood of the closed slit
  (`slit k = {‖w‖ = 1, Re(w^k) ≤ 0}`, which contains the punctures);
* `TwistedCc k ζ` — the sector: smooth across the slit with twist `ζ` (`TwistedPair.lean`);
* `NCc k`  — Neumann: no condition across the slit, only a one-sided smooth extension of each
  copy up to the slit (the paper's "restrictions to the hemispheres extend smoothly to the
  equator", `slit-density`).

For `1 ≤ k` and `ζ ≠ 0`, inclusions `DCc k ≤ TwistedCc k ζ ≤ NCc k` give the **index bracketing**
`ind_D ≤ ind_ζ ≤ ind_N` on every rotation eigenspace (`formIndex_bracket`) — the paper's
min-max inequalities, here by `formIndex_mono` alone.

The **copy swap** `swapF v n = v (n+1)` on the open disks (values on the circle kept, see the
docstring) is the reflection of `S²₃` through its equator; it preserves `NCc`, `DCc`, the
rotation eigenspaces and the form, and is an involution, so `CharDecomp` with `N = 2` splits the
Dirichlet and Neumann indices into even (`+1`) and odd (`−1`) parts (`formIndex_swap_split`):
the algebraic split underlying the paper's
`ind_N(S²₃) = ind_N(Ξ^{(0,π)}) + ind_{DN}(Ξ^{(0,π)})`.
The Neumann and Dirichlet split theorems here require `2 ≤ k`; identification
of their even/odd parts with single-disk boundary problems is separate.
-/
public import KsIndexLean.TwistedPair

@[expose] public section


noncomputable section

open Complex Real MeasureTheory Filter Topology
open scoped ContDiff

namespace KsIndex.Bracket

open KsIndex.Surface KsIndex.SurfaceForm KsIndex.SurfaceSym KsIndex.FormIndex KsIndex.Twisted
  KsIndex.GradOrtho

variable {k : ℕ}

/-! ### The reflection `σ(w) = 1/w̄` through the unit circle -/

/-- `σ w = 1 / w̄`, the reflection through the unit circle. -/
def σ (w : ℂ) : ℂ := 1 / (starRingEnd ℂ) w

lemma σ_apply (w : ℂ) : σ w = 1 / (starRingEnd ℂ) w := rfl

lemma σ_self {w : ℂ} (hw : ‖w‖ = 1) : σ w = w := by
  simp only [σ, one_div]
  exact inv_eq_of_mul_eq_one_right (by rw [Complex.conj_mul', hw]; norm_num)

lemma σ_σ (w : ℂ) : σ (σ w) = w := by
  simp [σ, map_inv₀]

lemma norm_σ (w : ℂ) : ‖σ w‖ = ‖w‖⁻¹ := by
  simp [σ, norm_inv]

lemma contDiffAt_σ {w₀ : ℂ} (hw0 : w₀ ≠ 0) : ContDiffAt ℝ ∞ σ w₀ := by
  have h1 : ContDiffAt ℝ ∞ (fun w : ℂ => (starRingEnd ℂ) w) w₀ := by
    have := (Complex.conjCLE.contDiff (n := ∞)).contDiffAt (x := w₀)
    exact this.congr_of_eventuallyEq (Eventually.of_forall fun w => by
      simp [Complex.conjCAE_apply])
  have h2 : ContDiffAt ℝ ∞ (Inv.inv : ℂ → ℂ) ((starRingEnd ℂ) w₀) :=
    contDiffAt_inv ℝ (by simpa using hw0)
  have : σ = fun w => ((starRingEnd ℂ) w)⁻¹ := funext fun w => by simp [σ]
  rw [this]
  exact h2.comp w₀ h1

lemma continuousAt_σ {w₀ : ℂ} (hw0 : w₀ ≠ 0) : ContinuousAt σ w₀ :=
  (contDiffAt_σ hw0).continuousAt

lemma not_norm_σ_le {w : ℂ} (hw0 : w ≠ 0) (hw : ‖w‖ < 1) : ¬ ‖σ w‖ ≤ 1 := by
  rw [norm_σ, not_le]
  exact (one_lt_inv₀ (norm_pos_iff.mpr hw0)).mpr hw

/-! ### The closed slit and the three test spaces -/

/-- The closed slit `{‖w‖ = 1, Re(w^k) ≤ 0}` = closure of `arcs_{k,0}`; contains the punctures. -/
def slit (k : ℕ) : Set ℂ := {w | ‖w‖ = 1 ∧ (w ^ k).re ≤ 0}

lemma arc_zero_subset_slit : arc k 0 ⊆ slit k := fun w hw =>
  ⟨hw.1, by have := hw.2; simp only [pow_zero, one_mul] at this; exact le_of_lt this⟩

lemma punctures_subset_slit (hk : 1 ≤ k) : punctures k ⊆ slit k := by
  intro p hp
  have hp' : p ^ (2 * k) = -1 := hp
  have hnorm : ‖p‖ = 1 := by
    have h1 : ‖p‖ ^ (2 * k) = 1 := by rw [← norm_pow, hp', norm_neg, norm_one]
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg p) (by omega)).mp h1
  refine ⟨hnorm, ?_⟩
  have hsq : (p ^ k) * (p ^ k) = -1 := by rw [← pow_add, ← two_mul, hp']
  have hre := congrArg Complex.re hsq
  have him := congrArg Complex.im hsq
  simp only [Complex.mul_re, Complex.mul_im, Complex.neg_re, Complex.one_re, Complex.neg_im,
    Complex.one_im, neg_zero] at hre him
  nlinarith [sq_nonneg ((p ^ k).re), sq_nonneg ((p ^ k).im)]

/-- One-sided smooth extension of `f` (defined on the disk) at a boundary point. -/
def OneSided (f : ℂ → ℂ) (w₀ : ℂ) : Prop :=
  ∃ F : ℂ → ℂ, ContDiffAt ℝ ∞ F w₀ ∧ ∀ᶠ w in 𝓝 w₀, w ∈ disk → f w = F w

lemma oneSided_zero (w₀ : ℂ) : OneSided 0 w₀ :=
  ⟨0, contDiffAt_const, Eventually.of_forall fun _ _ => rfl⟩

lemma oneSided_add {f g : ℂ → ℂ} {w₀ : ℂ} (hf : OneSided f w₀) (hg : OneSided g w₀) :
    OneSided (f + g) w₀ := by
  obtain ⟨F, hF, hFe⟩ := hf
  obtain ⟨G, hG, hGe⟩ := hg
  refine ⟨F + G, hF.add hG, ?_⟩
  filter_upwards [hFe, hGe] with w h1 h2 hw
  simp only [Pi.add_apply, h1 hw, h2 hw]

lemma oneSided_smul {f : ℂ → ℂ} {w₀ : ℂ} (c : ℂ) (hf : OneSided f w₀) :
    OneSided (c • f) w₀ := by
  obtain ⟨F, hF, hFe⟩ := hf
  refine ⟨c • F, hF.const_smul c, ?_⟩
  filter_upwards [hFe] with w h1 hw
  simp only [Pi.smul_apply, h1 hw]

/-- Neumann-type smoothness: smooth on the open disks, smooth across the seam `(0,1)`, one-sided
smooth at every point of `arcs_{k,0}` (the open slit) on each copy, vanishing outside `D̄`. -/
def IsSmoothN (k : ℕ) (v : ZMod (2 * 1) → ℂ → ℂ) : Prop :=
  (∀ n, ContDiffOn ℝ ∞ (v n) disk)
    ∧ (∀ w ∈ seamArc k 1 0, ContDiffAt ℝ ∞ (glue v 0) w)
    ∧ (∀ n, ∀ w ∈ arc k 0, OneSided (v n) w)
    ∧ (∀ n w, 1 < ‖w‖ → v n w = 0)

lemma isSmoothN_zero (k : ℕ) : IsSmoothN k 0 := by
  refine ⟨fun n => contDiffOn_const, fun w _ => ?_, fun n w _ => oneSided_zero w,
    fun n w _ => rfl⟩
  rw [glue_zero]; exact contDiffAt_const

lemma isSmoothN_add {u v : ZMod (2 * 1) → ℂ → ℂ} (hu : IsSmoothN k u) (hv : IsSmoothN k v) :
    IsSmoothN k (u + v) := by
  refine ⟨fun n => (hu.1 n).add (hv.1 n), fun w hw => ?_,
    fun n w hw => oneSided_add (hu.2.2.1 n w hw) (hv.2.2.1 n w hw), fun n w hw => ?_⟩
  · rw [glue_add]; exact (hu.2.1 w hw).add (hv.2.1 w hw)
  · simp only [Pi.add_apply, hu.2.2.2 n w hw, hv.2.2.2 n w hw, add_zero]

lemma isSmoothN_smul (c : ℂ) {u : ZMod (2 * 1) → ℂ → ℂ} (hu : IsSmoothN k u) :
    IsSmoothN k (c • u) := by
  refine ⟨fun n => (hu.1 n).const_smul c, fun w hw => ?_,
    fun n w hw => oneSided_smul c (hu.2.2.1 n w hw), fun n w hw => ?_⟩
  · rw [glue_smul]; exact (hu.2.1 w hw).const_smul c
  · simp only [Pi.smul_apply, hu.2.2.2 n w hw, smul_zero]

/-- The Neumann test space of the one-period (slit-sphere) problem. -/
def NCc (k : ℕ) : Submodule ℂ (ZMod (2 * 1) → ℂ → ℂ) where
  carrier := {v | IsSmoothN k v ∧ SuppAwayP k 1 v}
  zero_mem' := ⟨isSmoothN_zero k, suppAwayP_zero k 1⟩
  add_mem' := fun hu hv => ⟨isSmoothN_add hu.1 hv.1, suppAwayP_add hu.2 hv.2⟩
  smul_mem' := fun c _ hu => ⟨isSmoothN_smul c hu.1, suppAwayP_smul c hu.2⟩

/-- Vanishing on a neighbourhood of the closed slit. -/
def SuppAwaySlit (k : ℕ) (v : ZMod (2 * 1) → ℂ → ℂ) : Prop :=
  ∃ ε > 0, ∀ n w, (∃ p ∈ slit k, ‖w - p‖ < ε) → v n w = 0

lemma suppAwaySlit_zero (k : ℕ) : SuppAwaySlit k 0 := ⟨1, one_pos, fun _ _ _ => rfl⟩

lemma suppAwaySlit_add {u v : ZMod (2 * 1) → ℂ → ℂ} (hu : SuppAwaySlit k u)
    (hv : SuppAwaySlit k v) : SuppAwaySlit k (u + v) := by
  obtain ⟨ε₁, h₁, hu⟩ := hu
  obtain ⟨ε₂, h₂, hv⟩ := hv
  refine ⟨min ε₁ ε₂, lt_min h₁ h₂, fun n w hw => ?_⟩
  obtain ⟨p, hp, hwp⟩ := hw
  simp only [Pi.add_apply]
  rw [hu n w ⟨p, hp, lt_of_lt_of_le hwp (min_le_left _ _)⟩,
    hv n w ⟨p, hp, lt_of_lt_of_le hwp (min_le_right _ _)⟩, add_zero]

lemma suppAwaySlit_smul (c : ℂ) {u : ZMod (2 * 1) → ℂ → ℂ} (hu : SuppAwaySlit k u) :
    SuppAwaySlit k (c • u) := by
  obtain ⟨ε, hε, hu⟩ := hu
  exact ⟨ε, hε, fun n w hw => by simp only [Pi.smul_apply, hu n w hw, smul_zero]⟩

lemma suppAwayP_of_slit (hk : 1 ≤ k) {v : ZMod (2 * 1) → ℂ → ℂ} (hv : SuppAwaySlit k v) :
    SuppAwayP k 1 v := by
  obtain ⟨ε, hε, hv⟩ := hv
  exact ⟨ε, hε, fun n w ⟨p, hp, hwp⟩ => hv n w ⟨p, punctures_subset_slit hk hp, hwp⟩⟩

/-- Dirichlet-type smoothness: smooth on the disks, smooth across the seam `(0,1)`, vanishing
outside `D̄` (the slit condition is `SuppAwaySlit`). -/
def IsSmoothD (k : ℕ) (v : ZMod (2 * 1) → ℂ → ℂ) : Prop :=
  (∀ n, ContDiffOn ℝ ∞ (v n) disk)
    ∧ (∀ w ∈ seamArc k 1 0, ContDiffAt ℝ ∞ (glue v 0) w)
    ∧ (∀ n w, 1 < ‖w‖ → v n w = 0)

/-- The Dirichlet test space of the one-period (slit-sphere) problem. -/
def DCc (k : ℕ) : Submodule ℂ (ZMod (2 * 1) → ℂ → ℂ) where
  carrier := {v | IsSmoothD k v ∧ SuppAwaySlit k v}
  zero_mem' := ⟨⟨fun n => contDiffOn_const, fun w _ => by rw [glue_zero]; exact contDiffAt_const,
    fun n w _ => rfl⟩, suppAwaySlit_zero k⟩
  add_mem' := fun hu hv => ⟨⟨fun n => (hu.1.1 n).add (hv.1.1 n), fun w hw => by
      rw [glue_add]; exact (hu.1.2.1 w hw).add (hv.1.2.1 w hw), fun n w hw => by
      simp only [Pi.add_apply, hu.1.2.2 n w hw, hv.1.2.2 n w hw, add_zero]⟩,
    suppAwaySlit_add hu.2 hv.2⟩
  smul_mem' := fun c _ hu => ⟨⟨fun n => (hu.1.1 n).const_smul c, fun w hw => by
      rw [glue_smul]; exact (hu.1.2.1 w hw).const_smul c, fun n w hw => by
      simp only [Pi.smul_apply, hu.1.2.2 n w hw, smul_zero]⟩, suppAwaySlit_smul c hu.2⟩

/-- Uncurried versions. -/
def DomN (k : ℕ) : Submodule ℂ (ZMod (2 * 1) × ℂ → ℂ) := (NCc k).map (uncurryE 1).toLinearMap
def DomD (k : ℕ) : Submodule ℂ (ZMod (2 * 1) × ℂ → ℂ) := (DCc k).map (uncurryE 1).toLinearMap

lemma mem_DomN {V : ZMod (2 * 1) × ℂ → ℂ} : V ∈ DomN k ↔ (uncurryE 1).symm V ∈ NCc k :=
  Submodule.mem_map_equiv (NCc k)

lemma mem_DomD {V : ZMod (2 * 1) × ℂ → ℂ} : V ∈ DomD k ↔ (uncurryE 1).symm V ∈ DCc k :=
  Submodule.mem_map_equiv (DCc k)

/-! ### The inclusions `D ⊆ [ζ] ⊆ N` -/

/-- A slit point `w` (`‖w‖ = 1`): the points `z` with `z` and `σ z` both within `ε` of `w`
form a neighbourhood of `w`. -/
lemma eventually_near_slit {w : ℂ} (hw : ‖w‖ = 1) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ z in 𝓝 w, ‖z - w‖ < ε ∧ ‖σ z - w‖ < ε := by
  have hw0 : w ≠ 0 := by rintro rfl; simp at hw
  have h1 : ∀ᶠ z in 𝓝 w, ‖z - w‖ < ε := by
    have := Metric.ball_mem_nhds w hε
    filter_upwards [this] with z hz
    rwa [Metric.mem_ball, dist_eq_norm] at hz
  have h2 : ∀ᶠ z in 𝓝 w, ‖σ z - w‖ < ε := by
    have hc := (continuousAt_σ hw0).tendsto
    rw [σ_self hw] at hc
    have := hc (Metric.ball_mem_nhds w hε)
    filter_upwards [this] with z hz
    rwa [Set.mem_preimage, Metric.mem_ball, dist_eq_norm] at hz
  exact h1.and h2

theorem DCc_le_TwistedCc (hk : 1 ≤ k) (ζ : ℂ) : DCc k ≤ TwistedCc k ζ := by
  rintro v ⟨⟨h1, h2, h4⟩, hs⟩
  refine ⟨⟨h1, h2, fun w hw => ?_, h4⟩, suppAwayP_of_slit hk hs⟩
  obtain ⟨ε, hε, hz⟩ := hs
  rw [seamArc_one_one] at hw
  have hwslit : w ∈ slit k := arc_zero_subset_slit hw
  refine (contDiffAt_const (c := (0 : ℂ))).congr_of_eventuallyEq ?_
  filter_upwards [eventually_near_slit hw.1 hε] with z hz'
  show glueTw ζ v z = 0
  simp only [glueTw]
  split_ifs
  · exact hz 1 z ⟨w, hwslit, hz'.1⟩
  · rw [hz 0 (1 / (starRingEnd ℂ) z) ⟨w, hwslit, hz'.2⟩, mul_zero]

theorem TwistedCc_le_NCc {ζ : ℂ} (hζ : ζ ≠ 0) : TwistedCc k ζ ≤ NCc k := by
  rintro v ⟨⟨h1, h2, h3, h4⟩, hs⟩
  refine ⟨⟨h1, h2, fun n w hw => ?_, h4⟩, hs⟩
  have hw' : w ∈ seamArc k 1 1 := by rwa [seamArc_one_one]
  have hw0 : w ≠ 0 := by rintro rfl; have := hw.1; simp at this
  rcases (by decide : ∀ r : ZMod (2 * 1), r = 0 ∨ r = 1) n with rfl | rfl
  · -- copy 0: `ζ⁻¹ · glueTw ζ v ∘ σ`
    refine ⟨fun z => ζ⁻¹ * glueTw ζ v (σ z), ?_, ?_⟩
    · refine contDiffAt_const.mul ?_
      have hg : ContDiffAt ℝ ∞ (glueTw ζ v) (σ w) := by rw [σ_self hw.1]; exact h3 w hw'
      exact hg.comp w (contDiffAt_σ hw0)
    · filter_upwards [eventually_ne_nhds hw0] with z hzne hz
      have hgt := not_norm_σ_le hzne (mem_disk_iff.mp hz)
      simp only [glueTw, hgt, if_false]
      rw [show 1 / (starRingEnd ℂ) (σ z) = z by
        simp [σ, map_inv₀], ← mul_assoc, inv_mul_cancel₀ hζ, one_mul]
  · -- copy 1: `glueTw ζ v` itself
    refine ⟨glueTw ζ v, h3 w hw', Eventually.of_forall fun z hz => ?_⟩
    rw [glueTw, if_pos (le_of_lt (mem_disk_iff.mp hz))]

/-! ### Regularity of the Neumann space, and the sesquilinear structure -/

/-- Every member of the Neumann space is a regular family: interior points, punctures (zero),
slit points (one-sided extension), seam points (`glue v 0`, resp. `glue v 0 ∘ σ` on copy 1). -/
theorem regular_of_mem_NCc {v : ZMod (2 * 1) → ℂ → ℂ} (hv : v ∈ NCc k) : Regular v := by
  obtain ⟨⟨h1, h2, h3, h4⟩, ⟨ε, hε, hz⟩⟩ := hv
  refine ⟨h1, fun n w₀ hw₀ => ?_⟩
  rcases lt_or_eq_of_le hw₀ with hlt | heq
  · have hw : w₀ ∈ disk := mem_disk_iff.mpr hlt
    exact ⟨v n, (h1 n).contDiffAt (Metric.isOpen_ball.mem_nhds hw),
      Eventually.of_forall fun _ _ => rfl⟩
  by_cases hp : w₀ ∈ punctures k
  · refine ⟨0, contDiffAt_const, ?_⟩
    filter_upwards [Metric.ball_mem_nhds w₀ hε] with w hw _
    exact hz n w ⟨w₀, hp, by rwa [Metric.mem_ball, dist_eq_norm] at hw⟩
  rcases mem_arc_of_not_puncture heq hp with h0 | hA
  · exact h3 n w₀ h0
  have hA' : w₀ ∈ seamArc k 1 0 := by rwa [seamArc_one_zero]
  have hw0 : w₀ ≠ 0 := by rintro rfl; simp at heq
  rcases (by decide : ∀ r : ZMod (2 * 1), r = 0 ∨ r = 1) n with rfl | rfl
  · refine ⟨glue v 0, h2 w₀ hA', Eventually.of_forall fun w hw => ?_⟩
    rw [glue, if_pos (le_of_lt (mem_disk_iff.mp hw))]
  · refine ⟨glue v 0 ∘ σ, ?_, ?_⟩
    · have hg : ContDiffAt ℝ ∞ (glue v 0) (σ w₀) := by rw [σ_self heq]; exact h2 w₀ hA'
      exact hg.comp w₀ (contDiffAt_σ hw0)
    · filter_upwards [eventually_ne_nhds hw0] with w hwne hw
      have hgt := not_norm_σ_le hwne (mem_disk_iff.mp hw)
      simp only [Function.comp, glue, hgt, if_false, zero_add]
      congr 1
      simp [σ, map_inv₀]

theorem sesq_N (hk : 2 ≤ k) (E : Submodule ℂ (ZMod (2 * 1) × ℂ → ℂ)) :
    Sesq (Qs k 1) (Bs k 1) (DomN k ⊓ E) :=
  sesq_of_regular hk _ fun _ hU => regular_of_mem_NCc (mem_DomN.mp hU.1)

theorem sesq_D (hk : 2 ≤ k) (E : Submodule ℂ (ZMod (2 * 1) × ℂ → ℂ)) :
    Sesq (Qs k 1) (Bs k 1) (DomD k ⊓ E) :=
  sesq_of_regular hk _ fun _ hU => regular_of_mem_NCc
    (TwistedCc_le_NCc one_ne_zero (DCc_le_TwistedCc (by omega) 1 (mem_DomD.mp hU.1)))

/-! ### The index bracketing -/

/-- **Index bracketing** `ind_D ≤ ind_ζ ≤ ind_N` on any common subspace `E` (a rotation
eigenspace): the paper's min-max inequalities l.3854–3860, index half, by inclusion. -/
theorem formIndex_bracket (hk : 1 ≤ k) {ζ : ℂ} (hζ : ζ ≠ 0)
    (E : Submodule ℂ (ZMod (2 * 1) × ℂ → ℂ)) :
    formIndex (Qs k 1) (DomD k ⊓ E) ≤ formIndex (Qs k 1) (DomTw k ζ ⊓ E)
      ∧ formIndex (Qs k 1) (DomTw k ζ ⊓ E) ≤ formIndex (Qs k 1) (DomN k ⊓ E) :=
  ⟨formIndex_mono (inf_le_inf_right E (Submodule.map_mono (DCc_le_TwistedCc hk ζ))),
    formIndex_mono (inf_le_inf_right E (Submodule.map_mono (TwistedCc_le_NCc hζ)))⟩

/-! ### The copy swap (equator reflection) -/

/-- The copy swap on the OPEN disks: `swapF v n w = v (n+1) w` for `‖w‖ < 1`, and `v n w` on the
circle and outside.  (Values on the circle are kept: for a Neumann/Dirichlet pair the value of
copy `n` on the seam arc is the boundary value of BOTH copies there, while the other copy's
value on that arc is unconstrained — swapping it too would break the seam condition.) -/
def swapF (v : ZMod (2 * 1) → ℂ → ℂ) : ZMod (2 * 1) → ℂ → ℂ :=
  fun n w => if ‖w‖ < 1 then v (n + 1) w else v n w

/-- The copy swap on uncurried test functions. -/
def swapE : Module.End ℂ (ZMod (2 * 1) × ℂ → ℂ) where
  toFun U := fun p => if ‖p.2‖ < 1 then U (p.1 + 1, p.2) else U p
  map_add' _ _ := by funext p; simp only [Pi.add_apply]; split_ifs <;> rfl
  map_smul' _ _ := by funext p; simp only [Pi.smul_apply, RingHom.id_apply]; split_ifs <;> rfl

lemma swapE_apply (U : ZMod (2 * 1) × ℂ → ℂ) (p : ZMod (2 * 1) × ℂ) :
    swapE U p = if ‖p.2‖ < 1 then U (p.1 + 1, p.2) else U p := rfl

lemma uncurry_symm_swapE (U : ZMod (2 * 1) × ℂ → ℂ) :
    (uncurryE 1).symm (swapE U) = swapF ((uncurryE 1).symm U) := rfl

lemma add_one_add_one (n : ZMod (2 * 1)) : n + 1 + 1 = n := by revert n; decide

lemma one_add_one_zmod : (1 : ZMod (2 * 1)) + 1 = 0 := by decide

lemma swapE_sq (U : ZMod (2 * 1) × ℂ → ℂ) : (swapE ^ 2) U = U := by
  funext p
  rw [pow_two, Module.End.mul_apply]
  have e : ∀ (V : ZMod (2 * 1) × ℂ → ℂ) (q : ZMod (2 * 1) × ℂ),
      swapE V q = if ‖q.2‖ < 1 then V (q.1 + 1, q.2) else V q := fun _ _ => rfl
  simp only [e]
  by_cases h : ‖p.2‖ < 1
  · simp only [h, if_true, add_one_add_one]
  · simp only [h, if_false]

lemma swapF_eq_on_disk (v : ZMod (2 * 1) → ℂ → ℂ) (n : ZMod (2 * 1)) :
    ∀ w ∈ disk, swapF v n w = v (n + 1) w := fun w hw => by
  simp [swapF, mem_disk_iff.mp hw]

lemma swapF_eventuallyEq (v : ZMod (2 * 1) → ℂ → ℂ) (n : ZMod (2 * 1)) {w : ℂ} (hw : w ∈ disk) :
    swapF v n =ᶠ[𝓝 w] v (n + 1) :=
  eventually_of_mem (Metric.isOpen_ball.mem_nhds hw) (swapF_eq_on_disk v n)

lemma swapF_contDiffOn {v : ZMod (2 * 1) → ℂ → ℂ} (h : ∀ n, ContDiffOn ℝ ∞ (v n) disk)
    (n : ZMod (2 * 1)) : ContDiffOn ℝ ∞ (swapF v n) disk :=
  (h (n + 1)).congr (swapF_eq_on_disk v n)

/-- The glued swapped pair is the glued pair reflected: `glue (swapF v) 0 = glue v 0 ∘ σ` away
from `0`. -/
lemma glue_swapF (v : ZMod (2 * 1) → ℂ → ℂ) {z : ℂ} (hz : z ≠ 0) :
    glue (swapF v) 0 z = glue v 0 (σ z) := by
  have hpos : 0 < ‖z‖ := norm_pos_iff.mpr hz
  rcases lt_trichotomy ‖z‖ 1 with h | h | h
  · -- inside: both sides are `v 1 z`
    simp only [glue, swapF, ← σ_apply, zero_add, if_pos (le_of_lt h), if_pos h,
      if_neg (not_norm_σ_le hz h), σ_σ]
  · -- on the circle: `σ z = z`, both sides are `v 0 z`
    rw [σ_self h]
    have h1 : ¬ ‖z‖ < 1 := by rw [h]; exact lt_irrefl 1
    simp only [glue, swapF, zero_add, if_pos (le_of_eq h), if_neg h1]
  · -- outside: both sides are `v 0 (σ z)`
    have hσlt : ‖σ z‖ < 1 := by rw [norm_σ]; exact (inv_lt_one₀ hpos).mpr h
    simp only [glue, swapF, ← σ_apply, zero_add, one_add_one_zmod, if_neg (not_le.mpr h),
      if_pos hσlt, if_pos (le_of_lt hσlt)]

lemma swapF_seam {v : ZMod (2 * 1) → ℂ → ℂ} (h2 : ∀ w ∈ seamArc k 1 0, ContDiffAt ℝ ∞ (glue v 0) w)
    (w : ℂ) (hw : w ∈ seamArc k 1 0) : ContDiffAt ℝ ∞ (glue (swapF v) 0) w := by
  have hw1 : ‖w‖ = 1 := by rw [seamArc_one_zero] at hw; exact hw.1
  have hw0 : w ≠ 0 := by rintro rfl; simp at hw1
  have hg : ContDiffAt ℝ ∞ (glue v 0 ∘ σ) w := by
    have : ContDiffAt ℝ ∞ (glue v 0) (σ w) := by rw [σ_self hw1]; exact h2 w hw
    exact this.comp w (contDiffAt_σ hw0)
  refine hg.congr_of_eventuallyEq ?_
  filter_upwards [eventually_ne_nhds hw0] with z hz
  exact glue_swapF v hz

lemma swapF_mem_NCc {v : ZMod (2 * 1) → ℂ → ℂ} (hv : v ∈ NCc k) : swapF v ∈ NCc k := by
  obtain ⟨⟨h1, h2, h3, h4⟩, ⟨ε, hε, hz⟩⟩ := hv
  refine ⟨⟨swapF_contDiffOn h1, swapF_seam h2, fun n w hw => ?_, fun n w hw => ?_⟩,
    ⟨ε, hε, fun n w hw => ?_⟩⟩
  · obtain ⟨F, hF, hFe⟩ := h3 (n + 1) w hw
    refine ⟨F, hF, ?_⟩
    filter_upwards [hFe] with z h hz
    rw [swapF_eq_on_disk v n z hz, h hz]
  · simp only [swapF, if_neg (not_lt.mpr (le_of_lt hw))]; exact h4 n w hw
  · simp only [swapF]; split_ifs <;> exact hz _ w hw

lemma swapF_mem_DCc {v : ZMod (2 * 1) → ℂ → ℂ} (hv : v ∈ DCc k) : swapF v ∈ DCc k := by
  obtain ⟨⟨h1, h2, h4⟩, ⟨ε, hε, hz⟩⟩ := hv
  refine ⟨⟨swapF_contDiffOn h1, swapF_seam h2, fun n w hw => ?_⟩, ⟨ε, hε, fun n w hw => ?_⟩⟩
  · simp only [swapF, if_neg (not_lt.mpr (le_of_lt hw))]; exact h4 n w hw
  · simp only [swapF]; split_ifs <;> exact hz _ w hw

/-- The swap preserves the polarized form: on the open disks it permutes the two copies. -/
lemma jacobiB_swapF (k : ℕ) (u v : ZMod (2 * 1) → ℂ → ℂ) :
    jacobiB k 1 (swapF u) (swapF v) = jacobiB k 1 u v := by
  unfold jacobiB
  refine (Fintype.sum_equiv (Equiv.addRight (1 : ZMod (2 * 1))) _ _ fun n => ?_)
  simp only [Equiv.coe_addRight]
  congr 1
  · refine setIntegral_congr_fun measurableSet_disk fun w hw => ?_
    simp only [gradInner, (swapF_eventuallyEq u n hw).fderiv_eq,
      (swapF_eventuallyEq v n hw).fderiv_eq]
  · refine setIntegral_congr_fun measurableSet_disk fun w hw => ?_
    simp only [swapF_eq_on_disk u n w hw, swapF_eq_on_disk v n w hw]

lemma Bs_swapE (k : ℕ) (U V : ZMod (2 * 1) × ℂ → ℂ) :
    Bs k 1 (swapE U) (swapE V) = Bs k 1 U V := by
  simp only [Bs, uncurry_symm_swapE]
  exact jacobiB_swapF k _ _

/-- The swap commutes with rotations by unit complex numbers. -/
lemma swapE_rotE {a : ℂ} (ha : ‖a‖ = 1) (U : ZMod (2 * 1) × ℂ → ℂ) :
    swapE (rotE 1 a U) = rotE 1 a (swapE U) := by
  funext p
  simp only [swapE_apply, rotE_apply, norm_mul, ha, one_mul]

lemma swapE_mem_rot {a μ : ℂ} (ha : ‖a‖ = 1) {U : ZMod (2 * 1) × ℂ → ℂ}
    (hU : U ∈ Module.End.eigenspace (rotE 1 a) μ) :
    swapE U ∈ Module.End.eigenspace (rotE 1 a) μ := by
  rw [Module.End.mem_eigenspace_iff] at hU ⊢
  rw [← swapE_rotE ha, hU, map_smul]

lemma zeta_two : zeta 2 = -1 := by
  unfold zeta
  rw [show (2 * Real.pi * Complex.I / (2 : ℕ) : ℂ) = Real.pi * Complex.I by push_cast; ring]
  exact Complex.exp_pi_mul_I

/-- **Copy-swap splitting** of the index on any swap-stable domain of regular families: even
part (`swap = +1`) plus odd part (`swap = −1`). -/
theorem formIndex_swap_split {D : Submodule ℂ (ZMod (2 * 1) × ℂ → ℂ)}
    (hS : Sesq (Qs k 1) (Bs k 1) D) (hD : ∀ U ∈ D, swapE U ∈ D) :
    formIndex (Qs k 1) D
      = formIndex (Qs k 1) (D ⊓ Module.End.eigenspace swapE 1)
        + formIndex (Qs k 1) (D ⊓ Module.End.eigenspace swapE (-1)) := by
  have h := formIndex_eq_sum_eigen swapE hS (N := 2) two_pos (fun U _ => swapE_sq U) hD
    (fun U _ V _ => Bs_swapE k U V)
  rw [h, Fin.sum_univ_two]
  simp only [Fin.val_zero, Fin.val_one, pow_zero, pow_one, zeta_two]

/-- The Neumann index splits into even and odd parts, on each rotation eigenspace. -/
theorem formIndex_N_split (hk : 2 ≤ k) {a μ : ℂ} (ha : ‖a‖ = 1) :
    formIndex (Qs k 1) (DomN k ⊓ Module.End.eigenspace (rotE 1 a) μ)
      = formIndex (Qs k 1) ((DomN k ⊓ Module.End.eigenspace (rotE 1 a) μ)
          ⊓ Module.End.eigenspace swapE 1)
        + formIndex (Qs k 1) ((DomN k ⊓ Module.End.eigenspace (rotE 1 a) μ)
          ⊓ Module.End.eigenspace swapE (-1)) :=
  formIndex_swap_split (sesq_N hk _) fun U hU => by
    obtain ⟨hN, hR⟩ := Submodule.mem_inf.mp hU
    refine Submodule.mem_inf.mpr ⟨?_, swapE_mem_rot ha hR⟩
    rw [mem_DomN, uncurry_symm_swapE]
    exact swapF_mem_NCc (mem_DomN.mp hN)

/-- The Dirichlet index splits into even and odd parts, on each rotation eigenspace. -/
theorem formIndex_D_split (hk : 2 ≤ k) {a μ : ℂ} (ha : ‖a‖ = 1) :
    formIndex (Qs k 1) (DomD k ⊓ Module.End.eigenspace (rotE 1 a) μ)
      = formIndex (Qs k 1) ((DomD k ⊓ Module.End.eigenspace (rotE 1 a) μ)
          ⊓ Module.End.eigenspace swapE 1)
        + formIndex (Qs k 1) ((DomD k ⊓ Module.End.eigenspace (rotE 1 a) μ)
          ⊓ Module.End.eigenspace swapE (-1)) :=
  formIndex_swap_split (sesq_D hk _) fun U hU => by
    obtain ⟨hD, hR⟩ := Submodule.mem_inf.mp hU
    refine Submodule.mem_inf.mpr ⟨?_, swapE_mem_rot ha hR⟩
    rw [mem_DomD, uncurry_symm_swapE]
    exact swapF_mem_DCc (mem_DomD.mp hD)

end KsIndex.Bracket
