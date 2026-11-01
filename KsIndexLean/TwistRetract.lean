module

/-
# Boundary-continuous representatives of twisted rotation blocks

For `ζ ≠ 0` and `‖a‖ = 1`, `formIndex_DomTw_eq_c` proves that restricting
`DomTw k ζ ∩ eigenspace (rotE 1 a) μ` to the boundary-continuous subdomain
`DomTw_c k ζ` preserves its index for `Qs k 1`.

`Tfun` assigns each copy its limit from the open disk at points of the closed
disk, and assigns zero outside. For a `Regular` family, these limits exist.
The resulting function agrees pointwise with the original on the open disk
and is continuous on the closed disk. Boundary values may change: only the
copy read by each seam's gluing map is fixed by the original glue continuity.
That equality, together with the unchanged interior values, preserves the
glued functions on full neighborhoods of their respective seam arcs.

The map is linear on regular families, preserves vanishing near punctures,
and preserves the rotation eigenspace because unit-modulus rotations preserve
the disk. It also preserves `Qs`: local equality on the open disk preserves
both the values and derivatives appearing in its integrals. These properties
supply the form-preserving linear map used by `formIndex_eq_of_retraction`.
-/
public import KsIndexLean.TwistStable

@[expose] public section


noncomputable section

open Complex MeasureTheory Metric Filter Topology
open KsIndex.Surface KsIndex.SurfaceForm KsIndex.SurfaceSym KsIndex.Bracket KsIndex.Twisted
  KsIndex.FormIndex
open scoped ContDiff

namespace KsIndex.TwistSwap

variable {k : ℕ}

/-! ### The neighbourhood-within-disk filter -/

/-- Every point of the closed disk is in the closure of the open disk, so `𝓝[disk] w₀` is
nontrivial — the retraction reads a genuine (unique) limit there. -/
lemma nhdsWithin_disk_neBot {w₀ : ℂ} (hw₀ : ‖w₀‖ ≤ 1) : (𝓝[disk] w₀).NeBot := by
  have hmem : w₀ ∈ closure disk := by
    rw [disk, closure_ball (0 : ℂ) one_ne_zero]
    simp only [Metric.mem_closedBall, dist_zero_right]; exact hw₀
  exact mem_closure_iff_nhdsWithin_neBot.mp hmem

/-- Evaluation after uncurrying is evaluation on the corresponding pair. -/
lemma uncurry_symm_apply (U : ZMod (2 * 1) × ℂ → ℂ) (n : ZMod (2 * 1)) (z : ℂ) :
    (uncurryE 1).symm U n z = U (n, z) := rfl

/-! ### The boundary-limit retraction (raw function) -/

/-- **The boundary-limit retraction.**  On the closed disk, each copy is replaced by its
interior boundary limit; outside, by `0`.  Uniform over `‖w‖ ≤ 1` (no interior/circle split in
the definition): interior points automatically read the value (`𝓝[disk] w = 𝓝 w`). -/
def Tfun (U : ZMod (2 * 1) × ℂ → ℂ) : ZMod (2 * 1) × ℂ → ℂ :=
  fun p => if ‖p.2‖ ≤ 1 then limUnder (𝓝[disk] p.2) (fun z => U (p.1, z)) else 0

lemma Tfun_apply (U : ZMod (2 * 1) × ℂ → ℂ) (n : ZMod (2 * 1)) (w : ℂ) :
    Tfun U (n, w) = if ‖w‖ ≤ 1 then limUnder (𝓝[disk] w) (fun z => U (n, z)) else 0 := rfl

/-- On the closed disk a `Regular` copy converges within the disk, and `Tfun` reads that limit. -/
lemma tendsto_Tfun {U : ZMod (2 * 1) × ℂ → ℂ} (hU : Regular ((uncurryE 1).symm U))
    (n : ZMod (2 * 1)) {w : ℂ} (hw : ‖w‖ ≤ 1) :
    Tendsto (fun z => U (n, z)) (𝓝[disk] w) (𝓝 (Tfun U (n, w))) := by
  obtain ⟨F, hF, hFeq⟩ := hU.2 n w hw
  have hcong : (fun z => U (n, z)) =ᶠ[𝓝[disk] w] F := by
    filter_upwards [self_mem_nhdsWithin, hFeq.filter_mono nhdsWithin_le_nhds] with z hzd hzeq
    exact hzeq hzd
  have htend : Tendsto (fun z => U (n, z)) (𝓝[disk] w) (𝓝 (F w)) :=
    (hF.continuousAt.tendsto.mono_left nhdsWithin_le_nhds).congr' hcong.symm
  have := nhdsWithin_disk_neBot hw
  rw [Tfun_apply, if_pos hw, htend.limUnder_eq]
  exact htend

/-- On the open disk, `Tfun U = U` (interior limit = value). -/
lemma Tfun_eq_on_disk {U : ZMod (2 * 1) × ℂ → ℂ} (hU : Regular ((uncurryE 1).symm U))
    (n : ZMod (2 * 1)) {w : ℂ} (hw : w ∈ disk) : Tfun U (n, w) = U (n, w) := by
  have hwle : ‖w‖ ≤ 1 := le_of_lt (mem_disk_iff.mp hw)
  have htend := tendsto_Tfun hU n hwle
  have hca : Tendsto (fun z => U (n, z)) (𝓝[disk] w) (𝓝 (U (n, w))) := by
    have hc := ((hU.1 n).contDiffAt (Metric.isOpen_ball.mem_nhds hw)).continuousAt
    exact hc.tendsto.mono_left nhdsWithin_le_nhds
  have := nhdsWithin_disk_neBot hwle
  exact tendsto_nhds_unique htend hca

/-- On the open disk, the retracted copy agrees with the original on a full neighbourhood. -/
lemma Tfun_eventuallyEq_disk {U : ZMod (2 * 1) × ℂ → ℂ} (hU : Regular ((uncurryE 1).symm U))
    (n : ZMod (2 * 1)) {w : ℂ} (hw : w ∈ disk) :
    (uncurryE 1).symm (Tfun U) n =ᶠ[𝓝 w] (uncurryE 1).symm U n :=
  eventuallyEq_of_mem (Metric.isOpen_ball.mem_nhds hw) fun _ hz => Tfun_eq_on_disk hU n hz

/-- **Pinning.**  If a boundary-continuous representative `G` agrees with copy `n` on the closed
disk, then at a circle point the retraction returns the raw value (limit = value). -/
lemma pin_of_contAt {U : ZMod (2 * 1) × ℂ → ℂ} (hU : Regular ((uncurryE 1).symm U))
    (n : ZMod (2 * 1)) {w₀ : ℂ} (hw₀ : ‖w₀‖ = 1) {G : ℂ → ℂ} (hG : ContinuousAt G w₀)
    (hGeq : ∀ z, ‖z‖ ≤ 1 → G z = U (n, z)) : Tfun U (n, w₀) = U (n, w₀) := by
  have hwle : ‖w₀‖ ≤ 1 := le_of_eq hw₀
  have htend := tendsto_Tfun hU n hwle
  have hca : Tendsto (fun z => U (n, z)) (𝓝[disk] w₀) (𝓝 (U (n, w₀))) := by
    have e1 : Tendsto G (𝓝[disk] w₀) (𝓝 (G w₀)) := hG.tendsto.mono_left nhdsWithin_le_nhds
    have hGw₀ : G w₀ = U (n, w₀) := hGeq w₀ hwle
    have hcong : G =ᶠ[𝓝[disk] w₀] (fun z => U (n, z)) := by
      filter_upwards [self_mem_nhdsWithin] with z hz
      exact hGeq z (le_of_lt (mem_disk_iff.mp hz))
    rw [← hGw₀]; exact e1.congr' hcong
  have := nhdsWithin_disk_neBot hwle
  exact tendsto_nhds_unique htend hca

/-! ### Linearity of the retraction -/

lemma Tfun_add {U U' : ZMod (2 * 1) × ℂ → ℂ} (hU : Regular ((uncurryE 1).symm U))
    (hU' : Regular ((uncurryE 1).symm U')) : Tfun (U + U') = Tfun U + Tfun U' := by
  funext p
  obtain ⟨n, w⟩ := p
  simp only [Pi.add_apply]
  by_cases hwle : ‖w‖ ≤ 1
  · have := nhdsWithin_disk_neBot hwle
    have h := (tendsto_Tfun hU n hwle).add (tendsto_Tfun hU' n hwle)
    rw [Tfun_apply, if_pos hwle]
    exact h.limUnder_eq
  · rw [Tfun_apply, if_neg hwle, Tfun_apply, if_neg hwle, Tfun_apply, if_neg hwle, add_zero]

lemma Tfun_smul (c : ℂ) {U : ZMod (2 * 1) × ℂ → ℂ} (hU : Regular ((uncurryE 1).symm U)) :
    Tfun (c • U) = c • Tfun U := by
  funext p
  obtain ⟨n, w⟩ := p
  simp only [Pi.smul_apply, smul_eq_mul]
  by_cases hwle : ‖w‖ ≤ 1
  · have := nhdsWithin_disk_neBot hwle
    have h := (tendsto_Tfun hU n hwle).const_mul c
    rw [Tfun_apply, if_pos hwle]
    exact h.limUnder_eq
  · rw [Tfun_apply, if_neg hwle, Tfun_apply, if_neg hwle, mul_zero]

/-! ### The retracted copies are continuous up to the boundary (BdyCont) -/

lemma Tfun_continuousOn {U : ZMod (2 * 1) × ℂ → ℂ} (hU : Regular ((uncurryE 1).symm U))
    (n : ZMod (2 * 1)) :
    ContinuousOn (fun w => Tfun U (n, w)) (Metric.closedBall 0 1) := by
  intro w₀ hw₀
  have hnorm : ‖w₀‖ ≤ 1 := by rwa [Metric.mem_closedBall, dist_zero_right] at hw₀
  obtain ⟨F, hF, hFeq⟩ := hU.2 n w₀ hnorm
  have hFcont : ∀ᶠ y in 𝓝 w₀, ContinuousAt F y := by
    have h1 : ContDiffAt ℝ 1 F w₀ := hF.of_le (by exact_mod_cast le_top)
    filter_upwards [h1.eventually (by exact_mod_cast (by decide : (1 : ℕ∞) ≠ ⊤))] with y hy
      using hy.continuousAt
  have hFprop : ∀ᶠ y in 𝓝 w₀, ∀ᶠ z in 𝓝 y, z ∈ disk → (uncurryE 1).symm U n z = F z :=
    hFeq.eventually_nhds
  have key : ∀ᶠ w in 𝓝[Metric.closedBall (0 : ℂ) 1] w₀, (fun w => Tfun U (n, w)) w = F w := by
    have h1 := hFcont.filter_mono (nhdsWithin_le_nhds (s := Metric.closedBall (0 : ℂ) 1))
    have h2 := hFprop.filter_mono (nhdsWithin_le_nhds (s := Metric.closedBall (0 : ℂ) 1))
    filter_upwards [self_mem_nhdsWithin, h1, h2] with w hwcb hFw hpropw
    have hwle : ‖w‖ ≤ 1 := by rwa [Metric.mem_closedBall, dist_zero_right] at hwcb
    have := nhdsWithin_disk_neBot hwle
    have htend : Tendsto (fun z => U (n, z)) (𝓝[disk] w) (𝓝 (F w)) := by
      have e1 : Tendsto F (𝓝[disk] w) (𝓝 (F w)) := hFw.tendsto.mono_left nhdsWithin_le_nhds
      have e2 : (fun z => U (n, z)) =ᶠ[𝓝[disk] w] F := by
        filter_upwards [self_mem_nhdsWithin, hpropw.filter_mono nhdsWithin_le_nhds] with z hzd hzp
        exact hzp hzd
      exact e1.congr' e2.symm
    change Tfun U (n, w) = F w
    rw [Tfun_apply, if_pos hwle]
    exact htend.limUnder_eq
  have hval : (fun w => Tfun U (n, w)) w₀ = F w₀ := by
    have := nhdsWithin_disk_neBot hnorm
    have e2 : (fun z => U (n, z)) =ᶠ[𝓝[disk] w₀] F := by
      filter_upwards [self_mem_nhdsWithin, hFeq.filter_mono nhdsWithin_le_nhds] with z hzd hzp
      exact hzp hzd
    have htend : Tendsto (fun z => U (n, z)) (𝓝[disk] w₀) (𝓝 (F w₀)) :=
      (hF.continuousAt.tendsto.mono_left nhdsWithin_le_nhds).congr' e2.symm
    change Tfun U (n, w₀) = F w₀
    rw [Tfun_apply, if_pos hnorm]
    exact htend.limUnder_eq
  exact (hF.continuousAt.continuousWithinAt).congr_of_eventuallyEq key hval

/-! ### The retraction preserves the rotation eigenspace (E) -/

lemma Tfun_mem_eigenspace {a μ : ℂ} (ha : ‖a‖ = 1) {U : ZMod (2 * 1) × ℂ → ℂ}
    (hU : Regular ((uncurryE 1).symm U)) (hE : U ∈ Module.End.eigenspace (rotE 1 a) μ) :
    Tfun U ∈ Module.End.eigenspace (rotE 1 a) μ := by
  have ha0 : a ≠ 0 := by intro h; rw [h] at ha; simp at ha
  rw [Module.End.mem_eigenspace_iff] at hE ⊢
  have hErel : ∀ (n : ZMod (2 * 1)) (z : ℂ), U (n, a * z) = μ * U (n, z) := by
    intro n z
    have h := congr_fun hE (n, z)
    simpa only [rotE_apply, Pi.smul_apply, smul_eq_mul] using h
  funext p
  obtain ⟨n, w⟩ := p
  simp only [rotE_apply, Pi.smul_apply, smul_eq_mul]
  by_cases hwle : ‖w‖ ≤ 1
  · have hawle : ‖a * w‖ ≤ 1 := by rw [norm_mul, ha, one_mul]; exact hwle
    have htw := tendsto_Tfun hU n hwle
    have htaw := tendsto_Tfun hU n hawle
    have hinner : Tendsto (fun y => a⁻¹ * y) (𝓝[disk] (a * w)) (𝓝[disk] w) := by
      rw [tendsto_nhdsWithin_iff]
      refine ⟨?_, ?_⟩
      · have h0 : Tendsto (fun y : ℂ => a⁻¹ * y) (𝓝 (a * w)) (𝓝 (a⁻¹ * (a * w))) :=
          (continuous_const.mul continuous_id).tendsto _
        rw [← mul_assoc, inv_mul_cancel₀ ha0, one_mul] at h0
        exact h0.mono_left nhdsWithin_le_nhds
      · filter_upwards [self_mem_nhdsWithin] with y hy
        rw [mem_disk_iff] at hy ⊢
        rw [norm_mul, norm_inv, ha, inv_one, one_mul]; exact hy
    have hcomp : Tendsto (fun y => U (n, a⁻¹ * y)) (𝓝[disk] (a * w)) (𝓝 (Tfun U (n, w))) := by
      simpa only [Function.comp_def] using htw.comp hinner
    have hcomp2 := hcomp.const_mul μ
    have hfun : (fun y => μ * U (n, a⁻¹ * y)) = (fun y => U (n, y)) := by
      funext y
      have h := hErel n (a⁻¹ * y)
      rw [← mul_assoc, mul_inv_cancel₀ ha0, one_mul] at h
      exact h.symm
    rw [hfun] at hcomp2
    have := nhdsWithin_disk_neBot hawle
    exact tendsto_nhds_unique htaw hcomp2
  · have hawle : ¬ ‖a * w‖ ≤ 1 := by rw [norm_mul, ha, one_mul]; exact hwle
    rw [Tfun_apply, Tfun_apply, if_neg hawle, if_neg hwle, mul_zero]

/-! ### The retraction preserves the twisted domain (DomTw): seam neighbourhoods -/

/-- On the `glue`-seam family `arc k 1`, `glue (Tfun U) 0` agrees with `glue U 0` on a full
neighbourhood: interior/exterior read interior copy values (unchanged), the circle reads copy `0`
which is pinned by `glue`-continuity. -/
lemma glue0_Tfun_eventuallyEq {U : ZMod (2 * 1) × ℂ → ℂ} (hU : Regular ((uncurryE 1).symm U))
    (hc2 : ∀ w ∈ seamArc k 1 0, ContDiffAt ℝ ∞ (glue ((uncurryE 1).symm U) 0) w)
    {w₀ : ℂ} (hw₀ : w₀ ∈ arc k 1) :
    glue ((uncurryE 1).symm (Tfun U)) 0 =ᶠ[𝓝 w₀] glue ((uncurryE 1).symm U) 0 := by
  have hOopen : IsOpen {w : ℂ | 0 < (w ^ k).re} :=
    isOpen_lt continuous_const (Complex.continuous_re.comp (continuous_pow k))
  have hw₀O : w₀ ∈ {w : ℂ | 0 < (w ^ k).re} := by
    simp only [arc, Set.mem_ofPred_eq, pow_one, neg_one_mul] at hw₀
    exact by simpa only [Set.mem_ofPred_eq] using (by linarith [hw₀.2] : 0 < (w₀ ^ k).re)
  refine eventuallyEq_of_mem (hOopen.mem_nhds hw₀O) fun w hwO => ?_
  have hwO' : 0 < (w ^ k).re := hwO
  simp only [glue, uncurry_symm_apply, zero_add]
  rcases lt_trichotomy ‖w‖ 1 with hlt | heq | hgt
  · rw [if_pos (le_of_lt hlt), if_pos (le_of_lt hlt)]
    exact Tfun_eq_on_disk hU 0 (mem_disk_iff.mpr hlt)
  · rw [if_pos (le_of_eq heq), if_pos (le_of_eq heq)]
    have hwarc : w ∈ arc k 1 := by
      simp only [arc, Set.mem_ofPred_eq, pow_one, neg_one_mul]
      exact ⟨heq, by linarith⟩
    have hcont : ContinuousAt (glue ((uncurryE 1).symm U) 0) w :=
      (hc2 w (by rw [seamArc_one_zero]; exact hwarc)).continuousAt
    exact pin_of_contAt hU 0 heq hcont fun z hz => by
      simp only [glue, if_pos hz, uncurry_symm_apply]
  · have hσ : ‖(1 / (starRingEnd ℂ) w : ℂ)‖ < 1 := by
      rw [norm_div, norm_one, Complex.norm_conj]
      exact (div_lt_one (by linarith : (0 : ℝ) < ‖w‖)).mpr hgt
    rw [if_neg (not_le.mpr hgt), if_neg (not_le.mpr hgt)]
    exact Tfun_eq_on_disk hU 1 (mem_disk_iff.mpr hσ)

/-- On the `glueTw`-seam family `arc k 0`, `glueTw ζ (Tfun U)` agrees with `glueTw ζ U` on a full
neighbourhood: the circle reads copy `1`, pinned by `glueTw`-continuity. -/
lemma glueTw_Tfun_eventuallyEq {ζ : ℂ} {U : ZMod (2 * 1) × ℂ → ℂ}
    (hU : Regular ((uncurryE 1).symm U))
    (hc3 : ∀ w ∈ seamArc k 1 1, ContDiffAt ℝ ∞ (glueTw ζ ((uncurryE 1).symm U)) w)
    {w₀ : ℂ} (hw₀ : w₀ ∈ arc k 0) :
    glueTw ζ ((uncurryE 1).symm (Tfun U)) =ᶠ[𝓝 w₀] glueTw ζ ((uncurryE 1).symm U) := by
  have hOopen : IsOpen {w : ℂ | (w ^ k).re < 0} :=
    isOpen_lt (Complex.continuous_re.comp (continuous_pow k)) continuous_const
  have hw₀O : w₀ ∈ {w : ℂ | (w ^ k).re < 0} := by
    simp only [arc, Set.mem_ofPred_eq, pow_zero, one_mul] at hw₀
    exact hw₀.2
  refine eventuallyEq_of_mem (hOopen.mem_nhds hw₀O) fun w hwO => ?_
  have hwO' : (w ^ k).re < 0 := hwO
  simp only [glueTw, uncurry_symm_apply]
  rcases lt_trichotomy ‖w‖ 1 with hlt | heq | hgt
  · rw [if_pos (le_of_lt hlt), if_pos (le_of_lt hlt)]
    exact Tfun_eq_on_disk hU 1 (mem_disk_iff.mpr hlt)
  · rw [if_pos (le_of_eq heq), if_pos (le_of_eq heq)]
    have hwarc : w ∈ arc k 0 := by
      simp only [arc, Set.mem_ofPred_eq, pow_zero, one_mul]
      exact ⟨heq, hwO'⟩
    have hcont : ContinuousAt (glueTw ζ ((uncurryE 1).symm U)) w :=
      (hc3 w (by rw [seamArc_one_one]; exact hwarc)).continuousAt
    exact pin_of_contAt hU 1 heq hcont fun z hz => by
      simp only [glueTw, if_pos hz, uncurry_symm_apply]
  · have hσ : ‖(1 / (starRingEnd ℂ) w : ℂ)‖ < 1 := by
      rw [norm_div, norm_one, Complex.norm_conj]
      exact (div_lt_one (by linarith : (0 : ℝ) < ‖w‖)).mpr hgt
    rw [if_neg (not_le.mpr hgt), if_neg (not_le.mpr hgt)]
    congr 1
    exact Tfun_eq_on_disk hU 0 (mem_disk_iff.mpr hσ)

/-- The retraction preserves vanishing on a neighborhood of the puncture set. -/
lemma Tfun_suppAwayP {U : ZMod (2 * 1) × ℂ → ℂ}
    (hsupp : SuppAwayP k 1 ((uncurryE 1).symm U)) :
    SuppAwayP k 1 ((uncurryE 1).symm (Tfun U)) := by
  obtain ⟨ε₀, hε₀, hz₀⟩ := hsupp
  refine ⟨ε₀ / 2, by positivity, fun n w ⟨p, hp, hwp⟩ => ?_⟩
  change Tfun U (n, w) = 0
  by_cases hwle : ‖w‖ ≤ 1
  · have := nhdsWithin_disk_neBot hwle
    have hev : (fun z => U (n, z)) =ᶠ[𝓝[disk] w] (fun _ => (0 : ℂ)) := by
      have hball : Metric.ball w (ε₀ / 2) ∈ 𝓝[disk] w :=
        nhdsWithin_le_nhds (Metric.ball_mem_nhds w (by positivity))
      filter_upwards [hball] with z hz
      rw [Metric.mem_ball, dist_eq_norm] at hz
      have hzp : ‖z - p‖ < ε₀ := by
        calc ‖z - p‖ = ‖(z - w) + (w - p)‖ := by rw [sub_add_sub_cancel]
          _ ≤ ‖z - w‖ + ‖w - p‖ := norm_add_le _ _
          _ < ε₀ / 2 + ε₀ / 2 := add_lt_add hz hwp
          _ = ε₀ := by ring
      exact hz₀ n z ⟨p, hp, hzp⟩
    have htend : Tendsto (fun z => U (n, z)) (𝓝[disk] w) (𝓝 0) :=
      tendsto_const_nhds.congr' hev.symm
    rw [Tfun_apply, if_pos hwle]
    exact htend.limUnder_eq
  · rw [Tfun_apply, if_neg hwle]

/-! ### The retraction lands in `DomTw_c ⊓ E` -/

/-- `Regular` from membership in the twisted rotation block (through `NCc`). -/
lemma regFromDom {ζ a μ : ℂ} (hζ0 : ζ ≠ 0) {U : ZMod (2 * 1) × ℂ → ℂ}
    (hU : U ∈ DomTw k ζ ⊓ Module.End.eigenspace (rotE 1 a) μ) :
    Regular ((uncurryE 1).symm U) :=
  regular_of_mem_NCc (TwistedCc_le_NCc hζ0 (mem_DomTw.mp (Submodule.mem_inf.mp hU).1))

lemma Tfun_mem {ζ a μ : ℂ} (hζ0 : ζ ≠ 0) (ha : ‖a‖ = 1) {U : ZMod (2 * 1) × ℂ → ℂ}
    (hU : U ∈ DomTw k ζ ⊓ Module.End.eigenspace (rotE 1 a) μ) :
    Tfun U ∈ DomTw_c k ζ ⊓ Module.End.eigenspace (rotE 1 a) μ := by
  obtain ⟨hUD, hUE⟩ := Submodule.mem_inf.mp hU
  have hReg : Regular ((uncurryE 1).symm U) :=
    regular_of_mem_NCc (TwistedCc_le_NCc hζ0 (mem_DomTw.mp hUD))
  obtain ⟨⟨hc1, hc2, hc3, hc4⟩, hsupp⟩ := mem_DomTw.mp hUD
  have hTD : Tfun U ∈ DomTw k ζ := by
    rw [mem_DomTw]
    refine ⟨⟨fun n => ?_, fun w hw => ?_, fun w hw => ?_, fun n w hw => ?_⟩, ?_⟩
    · exact (hc1 n).congr fun z hz => by
        simp only [uncurry_symm_apply]; exact Tfun_eq_on_disk hReg n hz
    · have hwarc : w ∈ arc k 1 := by rw [← seamArc_one_zero]; exact hw
      exact (hc2 w hw).congr_of_eventuallyEq (glue0_Tfun_eventuallyEq hReg hc2 hwarc)
    · have hwarc : w ∈ arc k 0 := by rw [← seamArc_one_one]; exact hw
      exact (hc3 w hw).congr_of_eventuallyEq (glueTw_Tfun_eventuallyEq hReg hc3 hwarc)
    · change Tfun U (n, w) = 0
      rw [Tfun_apply, if_neg (not_le.mpr hw)]
    · exact Tfun_suppAwayP hsupp
  have hTB : Tfun U ∈ BdyCont := by
    rw [mem_BdyCont]; intro n; exact Tfun_continuousOn hReg n
  have hTE : Tfun U ∈ Module.End.eigenspace (rotE 1 a) μ := Tfun_mem_eigenspace ha hReg hUE
  exact Submodule.mem_inf.mpr ⟨Submodule.mem_inf.mpr ⟨hTD, hTB⟩, hTE⟩

/-! ### The retraction preserves the Jacobi form -/

lemma Tfun_preserves_Q {U : ZMod (2 * 1) × ℂ → ℂ} (hU : Regular ((uncurryE 1).symm U)) :
    Qs k 1 (Tfun U) = Qs k 1 U := by
  simp only [Qs, jacobiQ]
  refine Finset.sum_congr rfl fun n _ => ?_
  congr 1
  · simp only [dirichletG]
    refine setIntegral_congr_fun measurableSet_disk fun w hw => ?_
    have hgs : gradSq ((uncurryE 1).symm (Tfun U) n) w = gradSq ((uncurryE 1).symm U n) w := by
      simp only [gradSq, (Tfun_eventuallyEq_disk hU n hw).fderiv_eq]
    rw [hgs]
  · simp only [potentialG]
    refine setIntegral_congr_fun measurableSet_disk fun w hw => ?_
    have hval : (uncurryE 1).symm (Tfun U) n w = (uncurryE 1).symm U n w :=
      Tfun_eq_on_disk hU n hw
    rw [hval]

lemma Qs_zero : Qs k 1 (0 : ZMod (2 * 1) × ℂ → ℂ) = 0 := by
  simp only [Qs, map_zero, jacobiQ, Pi.zero_apply]
  simp only [dirichletG, potentialG, gradSq]
  simp

/-! ### Equality of the form indices -/

/-- **Boundary-continuous representatives preserve the index.** For `ζ ≠ 0` and `‖a‖ = 1`, on the twisted
rotation block, restricting to the boundary-continuous subdomain `DomTw_c` does not change the
Morse index — the boundary-limit retraction `Tfun` maps the block into `DomTw_c ⊓ E`, is linear,
and preserves `Qs`. -/
theorem formIndex_DomTw_eq_c {ζ a μ : ℂ} (hζ0 : ζ ≠ 0) (ha : ‖a‖ = 1) :
    formIndex (Qs k 1) (DomTw k ζ ⊓ Module.End.eigenspace (rotE 1 a) μ)
      = formIndex (Qs k 1) (DomTw_c k ζ ⊓ Module.End.eigenspace (rotE 1 a) μ) := by
  set D := DomTw k ζ ⊓ Module.End.eigenspace (rotE 1 a) μ with hDdef
  set D' := DomTw_c k ζ ⊓ Module.End.eigenspace (rotE 1 a) μ with hD'def
  have hD'D : D' ≤ D := inf_le_inf_right _ (DomTw_c_le_DomTw k ζ)
  let T : ↥D →ₗ[ℂ] (ZMod (2 * 1) × ℂ → ℂ) :=
    { toFun := fun U => Tfun U.val
      map_add' := fun U U' => Tfun_add (regFromDom hζ0 U.2) (regFromDom hζ0 U'.2)
      map_smul' := fun c U => Tfun_smul c (regFromDom hζ0 U.2) }
  have hTmem : ∀ U : ↥D, T U ∈ D' := fun U => Tfun_mem hζ0 ha U.2
  have hTQ : ∀ U : ↥D, Qs k 1 (T U) = Qs k 1 (U : ZMod (2 * 1) × ℂ → ℂ) :=
    fun U => Tfun_preserves_Q (regFromDom hζ0 U.2)
  exact formIndex_eq_of_retraction Qs_zero hD'D T hTmem hTQ

end KsIndex.TwistSwap
