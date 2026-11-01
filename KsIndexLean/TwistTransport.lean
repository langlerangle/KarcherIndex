module

/-
KsIndexLean — Twisted seam transport to a single-disk reflection space.

Restriction to copy `0` transports the `ε` eigenspace of `swapTwE ζ` in the
boundary-continuous domain `DomTw_c k ζ` to `ReflCc k (ε * ζ) ε`. The swap
relation gives `v₁ = (ε * ζ) * v₀` at every point when `ζ² = 1`. With `ε² = 1`,
the two gluing conditions become reflection conditions with signs `ε * ζ`
on `arc_1` and `ε` on `arc_0`.

`ReflCc` includes continuity on the closed disk, smoothness in the open disk
and across the reflected arcs, vanishing outside the disk, and vanishing near
the punctures. Closed-disk continuity is retained by restriction and by the
reverse extension `extR`; the transport uses `DomTw_c`, which includes this
boundary condition.

For `ζ² = ε² = 1` and `‖ζ‖ = ‖ε‖ = 1`, `seam_transport_tw` identifies the two
form indices on corresponding rotation eigenspaces. It uses
`Qs k 1 = 2 * Qd k` on the swap eigenspace and positivity of the factor `2`.
The rotation parameters `a` and `μ` are arbitrary complex numbers; this
transport theorem has no lower bound on `k`. Identification with paper seam
counts is a separate result.
-/
public import KsIndexLean.SingleDisk
public import KsIndexLean.TwistSplit

@[expose] public section


noncomputable section

open Complex Real MeasureTheory Filter Topology Metric
open scoped ContDiff

namespace KsIndex.TwistSwap

open KsIndex.Surface KsIndex.SurfaceForm KsIndex.SurfaceSym KsIndex.FormIndex KsIndex.Twisted
  KsIndex.Bracket KsIndex.SingleDiskBridge KsIndex.SingleDisk

variable {k : ℕ}

/-! ### The `swapTwE` eigen-condition -/

/-- The twisted-swap eigen-condition, pointwise (no `‖w‖` gate). -/
lemma mem_swapTw_iff {ζ ε : ℂ} {U : ZMod (2 * 1) × ℂ → ℂ} :
    U ∈ Module.End.eigenspace (swapTwE ζ) ε
      ↔ ∀ p : ZMod (2 * 1) × ℂ, ζ * U (p.1 + 1, p.2) = ε * U p := by
  rw [Module.End.mem_eigenspace_iff]
  constructor
  · intro h p
    have := congr_fun h p
    simpa only [swapTwE_apply, Pi.smul_apply, smul_eq_mul] using this
  · intro h
    funext p
    simp only [swapTwE_apply, Pi.smul_apply, smul_eq_mul]
    exact h p

/-! ### The single-disk reflection space `ReflCc` -/

/-- The single-disk smoothness/boundary package with reflection sign `s₁` across `arc_1` and `s₀`
across `arc_0` (both arcs REFLECTION-encoded, unlike `SingleCc` which is natural on `arc_0`).  The
`ContinuousOn (closedBall 0 1)` clause records boundary-continuity (inherited from `DomTw_c`), which
is what lets the reverse extension land back in `DomTw_c`. -/
def IsSmoothR (k : ℕ) (s₁ s₀ : ℂ) (f : ℂ → ℂ) : Prop :=
  ContDiffOn ℝ ∞ f disk
    ∧ (∀ w ∈ arc k 1, ContDiffAt ℝ ∞ (refl s₁ f) w)
    ∧ (∀ w ∈ arc k 0, ContDiffAt ℝ ∞ (refl s₀ f) w)
    ∧ (∀ w, 1 < ‖w‖ → f w = 0)
    ∧ SuppAwayP1 k f
    ∧ ContinuousOn f (closedBall 0 1)

lemma isSmoothR_zero (k : ℕ) (s₁ s₀ : ℂ) : IsSmoothR k s₁ s₀ 0 := by
  refine ⟨contDiffOn_const, fun w _ => ?_, fun w _ => ?_, fun _ _ => rfl,
    ⟨1, one_pos, fun _ _ => rfl⟩, continuousOn_const⟩
  · rw [refl_zero]; exact contDiffAt_const
  · rw [refl_zero]; exact contDiffAt_const

lemma isSmoothR_add {s₁ s₀ : ℂ} {f g : ℂ → ℂ} (hf : IsSmoothR k s₁ s₀ f)
    (hg : IsSmoothR k s₁ s₀ g) : IsSmoothR k s₁ s₀ (f + g) := by
  obtain ⟨f1, f2, f3, f4, ⟨εf, hεf, f5⟩, f6⟩ := hf
  obtain ⟨g1, g2, g3, g4, ⟨εg, hεg, g5⟩, g6⟩ := hg
  refine ⟨f1.add g1, fun w hw => ?_, fun w hw => ?_, fun w hw => ?_,
    ⟨min εf εg, lt_min hεf hεg, fun w ⟨p, hp, hwp⟩ => ?_⟩, f6.add g6⟩
  · rw [refl_add]; exact (f2 w hw).add (g2 w hw)
  · rw [refl_add]; exact (f3 w hw).add (g3 w hw)
  · simp only [Pi.add_apply, f4 w hw, g4 w hw, add_zero]
  · simp only [Pi.add_apply, f5 w ⟨p, hp, lt_of_lt_of_le hwp (min_le_left _ _)⟩,
      g5 w ⟨p, hp, lt_of_lt_of_le hwp (min_le_right _ _)⟩, add_zero]

lemma isSmoothR_smul {s₁ s₀ : ℂ} (c : ℂ) {f : ℂ → ℂ} (hf : IsSmoothR k s₁ s₀ f) :
    IsSmoothR k s₁ s₀ (c • f) := by
  obtain ⟨f1, f2, f3, f4, ⟨ε, hε, f5⟩, f6⟩ := hf
  refine ⟨f1.const_smul c, fun w hw => ?_, fun w hw => ?_, fun w hw => ?_,
    ⟨ε, hε, fun w hw => ?_⟩, f6.const_smul c⟩
  · rw [refl_smul]; exact (f2 w hw).const_smul c
  · rw [refl_smul]; exact (f3 w hw).const_smul c
  · simp only [Pi.smul_apply, f4 w hw, smul_zero]
  · simp only [Pi.smul_apply, f5 w hw, smul_zero]

/-- **The single-disk reflection space** with reflection sign `s₁` across `arc_1`, `s₀` across
`arc_0`.  The `(ζ,ε)` swap eigenspace restricts to `ReflCc k (ε·ζ) ε`. -/
def ReflCc (k : ℕ) (s₁ s₀ : ℂ) : Submodule ℂ (ℂ → ℂ) where
  carrier := {f | IsSmoothR k s₁ s₀ f}
  zero_mem' := isSmoothR_zero k s₁ s₀
  add_mem' := fun hf hg => isSmoothR_add hf hg
  smul_mem' := fun c _ hf => isSmoothR_smul c hf

lemma mem_ReflCc {s₁ s₀ : ℂ} {f : ℂ → ℂ} : f ∈ ReflCc k s₁ s₀ ↔ IsSmoothR k s₁ s₀ f :=
  Iff.rfl

/-! ### The reverse extension `extR` -/

/-- The reflection extension of a single-disk function to a twisted pair: copy `0` is `f`, copy `1`
is `c · f` EVERYWHERE (matching `swapTwE`'s gate-free convention, unlike `extS`). -/
def extR (c : ℂ) : (ℂ → ℂ) →ₗ[ℂ] (ZMod (2 * 1) × ℂ → ℂ) where
  toFun f := fun p => if p.1 = 0 then f p.2 else c * f p.2
  map_add' _ _ := by funext p; simp only [Pi.add_apply]; split_ifs <;> ring
  map_smul' _ _ := by
    funext p; simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; split_ifs <;> ring

lemma extR_zero (c : ℂ) (f : ℂ → ℂ) (w : ℂ) : extR c f (0, w) = f w := by simp [extR]

lemma extR_one (c : ℂ) (f : ℂ → ℂ) (w : ℂ) : extR c f (1, w) = c * f w := by
  simp [extR, show (1 : ZMod (2 * 1)) ≠ 0 by decide]

lemma res0_extR (c : ℂ) (f : ℂ → ℂ) : res0 (extR c f) = f :=
  funext fun w => extR_zero c f w

/-! ### The form: `Qs k 1 = 2 · Qd k` on a `swapTwE`-eigenspace -/

lemma Qs_eq_two_Qd_tw {ζ ε : ℂ} (hζ2 : ζ ^ 2 = 1) (hζ : ‖ζ‖ = 1) (hε : ‖ε‖ = 1)
    {U : ZMod (2 * 1) × ℂ → ℂ} (hS : U ∈ Module.End.eigenspace (swapTwE ζ) ε) :
    Qs k 1 U = 2 * Qd k (res0 U) := by
  have hS' := mem_swapTw_iff.mp hS
  simp only [Qs, jacobiQ]
  rw [sum_zmod_two]
  set v := (uncurryE 1).symm U with hv
  have hv1 : v 1 = fun w => (ε * ζ) * v 0 w := by
    funext w
    have hev : ζ * v 1 w = ε * v 0 w := by
      have := hS' (0, w); rw [zero_add] at this; exact this
    linear_combination ζ * hev - v 1 w * hζ2
  have hcnorm : ‖ε * ζ‖ = 1 := by rw [norm_mul, hε, hζ, one_mul]
  have hres : res0 U = v 0 := rfl
  have h1 : dirichletG k (v 1) - potentialG k (v 1) = dirichletG k (v 0) - potentialG k (v 0) := by
    rw [hv1]; exact summand_unit_mul k hcnorm (v 0)
  rw [h1, hres, Qd]; ring

/-! ### Restriction lands in the reflection space -/

lemma res_mem_tw {ζ ε a μ : ℂ} (hζ2 : ζ ^ 2 = 1) (hε2 : ε ^ 2 = 1)
    {U : ZMod (2 * 1) × ℂ → ℂ}
    (hU : U ∈ (DomTw_c k ζ ⊓ Module.End.eigenspace (rotE 1 a) μ)
      ⊓ Module.End.eigenspace (swapTwE ζ) ε) :
    res0 U ∈ ReflCc k (ε * ζ) ε ⊓ Module.End.eigenspace (rot1 a) μ := by
  obtain ⟨⟨hDc, hR⟩, hS⟩ := hU
  obtain ⟨hUD, hUB⟩ := Submodule.mem_inf.mp hDc
  obtain ⟨⟨hc1, hc2, hc3, hc4⟩, hsupp⟩ := mem_DomTw.mp hUD
  have hbc : ∀ n, ContinuousOn ((uncurryE 1).symm U n) (closedBall 0 1) := mem_BdyCont.mp hUB
  have hζne : ζ ≠ 0 := by rintro rfl; simp at hζ2
  have hεne : ε ≠ 0 := by rintro rfl; simp at hε2
  have hcne : ε * ζ ≠ 0 := mul_ne_zero hεne hζne
  set v := (uncurryE 1).symm U with hv
  have hS' := mem_swapTw_iff.mp hS
  have hv1 : ∀ w, v 1 w = (ε * ζ) * v 0 w := by
    intro w
    have hev : ζ * v 1 w = ε * v 0 w := by
      have := hS' (0, w); rw [zero_add] at this; exact this
    linear_combination ζ * hev - v 1 w * hζ2
  have hglue0 : glue v 0 = refl (ε * ζ) (v 0) := by
    funext w
    by_cases hz : ‖w‖ ≤ 1
    · simp only [glue, SingleDisk.refl, if_pos hz, zero_add]
    · simp only [glue, SingleDisk.refl, if_neg hz, zero_add]
      rw [show (σ w) = 1 / (starRingEnd ℂ) w from rfl, hv1 (1 / (starRingEnd ℂ) w)]
  have hglueTw : glueTw ζ v = (ε * ζ) • refl ε (v 0) := by
    funext w
    simp only [Pi.smul_apply, smul_eq_mul]
    by_cases hz : ‖w‖ ≤ 1
    · simp only [glueTw, SingleDisk.refl, if_pos hz, hv1 w]
    · simp only [glueTw, SingleDisk.refl, if_neg hz]
      rw [show (σ w) = 1 / (starRingEnd ℂ) w from rfl]
      linear_combination (-(ζ * v 0 (1 / (starRingEnd ℂ) w))) * hε2
  refine Submodule.mem_inf.mpr ⟨?_, ?_⟩
  · have hres : res0 U = v 0 := rfl
    rw [hres, mem_ReflCc]
    refine ⟨hc1 0, ?_, ?_, hc4 0, ?_, hbc 0⟩
    · intro w hw
      rw [← hglue0]
      exact hc2 w (by rw [seamArc_one_zero]; exact hw)
    · intro w hw
      have h := hc3 w (by rw [seamArc_one_one]; exact hw)
      rw [hglueTw] at h
      have h2 := h.const_smul (ε * ζ)⁻¹
      simpa only [Pi.smul_apply, smul_smul, inv_mul_cancel₀ hcne, one_smul] using h2
    · obtain ⟨εs, hεs, hz⟩ := hsupp
      exact ⟨εs, hεs, fun w hw => hz 0 w hw⟩
  · have hR' := Module.End.mem_eigenspace_iff.mp hR
    rw [Module.End.mem_eigenspace_iff]
    funext w
    exact congr_fun hR' (0, w)

/-! ### Extension lands in the boundary-continuous twisted domain -/

lemma extR_mem_DomTw_c {ζ ε : ℂ} (hε2 : ε ^ 2 = 1) {f : ℂ → ℂ}
    (hf : f ∈ ReflCc k (ε * ζ) ε) : extR (ε * ζ) f ∈ DomTw_c k ζ := by
  obtain ⟨hf1, hf2, hf3, hf4, hf5, hf6⟩ := mem_ReflCc.mp hf
  set v := (uncurryE 1).symm (extR (ε * ζ) f) with hv
  have hv0 : ∀ w, v 0 w = f w := fun w => extR_zero (ε * ζ) f w
  have hv1 : ∀ w, v 1 w = (ε * ζ) * f w := fun w => extR_one (ε * ζ) f w
  have hv0' : v 0 = f := funext hv0
  have hv1' : v 1 = (ε * ζ) • f := funext fun w => by
    rw [hv1 w]; simp only [Pi.smul_apply, smul_eq_mul]
  have hglue0 : glue v 0 = refl (ε * ζ) f := by
    funext w
    by_cases hz : ‖w‖ ≤ 1
    · simp only [glue, SingleDisk.refl, if_pos hz, zero_add, hv0 w]
    · simp only [glue, SingleDisk.refl, if_neg hz, zero_add]
      rw [hv1 (1 / (starRingEnd ℂ) w), show (σ w) = 1 / (starRingEnd ℂ) w from rfl]
  have hglueTw : glueTw ζ v = (ε * ζ) • refl ε f := by
    funext w
    simp only [Pi.smul_apply, smul_eq_mul]
    by_cases hz : ‖w‖ ≤ 1
    · simp only [glueTw, SingleDisk.refl, if_pos hz, hv1 w]
    · simp only [glueTw, SingleDisk.refl, if_neg hz, hv0 (1 / (starRingEnd ℂ) w)]
      rw [show (σ w) = 1 / (starRingEnd ℂ) w from rfl]
      linear_combination (-(ζ * f (1 / (starRingEnd ℂ) w))) * hε2
  refine Submodule.mem_inf.mpr ⟨?_, ?_⟩
  · rw [mem_DomTw, ← hv]
    refine ⟨⟨fun n => ?_, fun w hw => ?_, fun w hw => ?_, fun n w hw => ?_⟩, ?_⟩
    · rcases zmod_two_cases n with rfl | rfl
      · rw [hv0']; exact hf1
      · rw [hv1']; exact hf1.const_smul (ε * ζ)
    · rw [hglue0]
      exact hf2 w (by rwa [seamArc_one_zero] at hw)
    · rw [hglueTw]
      exact (hf3 w (by rwa [seamArc_one_one] at hw)).const_smul (ε * ζ)
    · rcases zmod_two_cases n with rfl | rfl
      · rw [hv0 w]; exact hf4 w hw
      · rw [hv1 w, hf4 w hw, mul_zero]
    · obtain ⟨εs, hεs, hz⟩ := hf5
      refine ⟨εs, hεs, fun n w hw => ?_⟩
      rcases zmod_two_cases n with rfl | rfl
      · rw [hv0 w]; exact hz w hw
      · rw [hv1 w, hz w hw, mul_zero]
  · rw [mem_BdyCont]
    intro n
    rcases zmod_two_cases n with rfl | rfl
    · have he : (fun w => extR (ε * ζ) f (0, w)) = f := funext fun w => extR_zero (ε * ζ) f w
      rw [he]; exact hf6
    · have he : (fun w => extR (ε * ζ) f (1, w)) = (ε * ζ) • f :=
        funext fun w => by rw [extR_one]; simp only [Pi.smul_apply, smul_eq_mul]
      rw [he]; exact hf6.const_smul (ε * ζ)

lemma extR_mem_rot {a μ c : ℂ} {f : ℂ → ℂ}
    (hf : f ∈ Module.End.eigenspace (rot1 a) μ) :
    extR c f ∈ Module.End.eigenspace (rotE 1 a) μ := by
  rw [Module.End.mem_eigenspace_iff] at hf ⊢
  have hcomm : rotE 1 a (extR c f) = extR c (rot1 a f) := by
    funext p
    simp only [rotE_apply, extR, LinearMap.coe_mk, AddHom.coe_mk, rot1_apply]
  rw [hcomm, hf, map_smul]

lemma extR_mem_swapTw {ζ ε : ℂ} (hζ2 : ζ ^ 2 = 1) (hε2 : ε ^ 2 = 1) (f : ℂ → ℂ) :
    extR (ε * ζ) f ∈ Module.End.eigenspace (swapTwE ζ) ε := by
  rw [mem_swapTw_iff]
  rintro ⟨n, w⟩
  rcases zmod_two_cases n with rfl | rfl
  · simp only [zero_add, extR_one, extR_zero]
    linear_combination (ε * f w) * hζ2
  · simp only [show (1 + 1 : ZMod (2 * 1)) = 0 by decide, extR_zero, extR_one]
    linear_combination (-(ζ * f w)) * hε2

/-! ### The twisted seam transport -/

/-- **Twisted seam transport.**  The `ε`-swap-part of the twisted-pair problem with
twist `ζ` on the rotation eigenspace `E_rot(a, μ)` has the index of the one-disk form `Qd k` on the
reflection space `ReflCc k (ε·ζ) ε ⊓ E_rot1(a, μ)` (restriction to copy `0` ⇄ reflection extension
`extR (ε·ζ)`; `Qs k 1 = 2·Qd k` on the swap-eigenpart). -/
theorem seam_transport_tw {ζ ε a μ : ℂ} (hζ2 : ζ ^ 2 = 1) (hε2 : ε ^ 2 = 1)
    (hζ1 : ‖ζ‖ = 1) (hε1 : ‖ε‖ = 1) :
    formIndex (Qs k 1) ((DomTw_c k ζ ⊓ Module.End.eigenspace (rotE 1 a) μ)
        ⊓ Module.End.eigenspace (swapTwE ζ) ε)
      = formIndex (Qd k) (ReflCc k (ε * ζ) ε ⊓ Module.End.eigenspace (rot1 a) μ) := by
  rw [← formIndex_smul_pos (Q := Qd k)
    (D := ReflCc k (ε * ζ) ε ⊓ Module.End.eigenspace (rot1 a) μ) (two_pos : (0 : ℝ) < 2)]
  refine formIndex_transport_surj res0 (fun U hU => ?_) (fun f hf => ?_) (fun U hU => ?_) ?_
  · exact res_mem_tw hζ2 hε2 hU
  · obtain ⟨hf1, hf2⟩ := Submodule.mem_inf.mp hf
    refine ⟨extR (ε * ζ) f, ?_, res0_extR _ _⟩
    exact Submodule.mem_inf.mpr ⟨Submodule.mem_inf.mpr
      ⟨extR_mem_DomTw_c hε2 hf1, extR_mem_rot hf2⟩, extR_mem_swapTw hζ2 hε2 f⟩
  · exact Qs_eq_two_Qd_tw hζ2 hζ1 hε1 hU.2
  · rw [Qd_zero, mul_zero]

end KsIndex.TwistSwap
