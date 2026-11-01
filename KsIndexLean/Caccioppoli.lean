module

/-
Finite Dirichlet energy of bounded smooth Jacobi fields.

For `k ≥ 2` and nonzero `m`, `bddJacobi_le_energySmooth` proves
`BoundedJacobi k m ≤ EnergySmooth k m`. Smoothness, puncture normalization
and seam values are shared carrier conditions; boundedness gives finite L²
mass on the finite-measure disks. The remaining condition is integrability
of `gradSq` on each disk.

The truncated Caccioppoli estimate sums first-Green identities over the `2m`
copies. Testing `Δu = −potV·u` against `(cutP)²·u` leaves seam boundary fluxes,
which cancel pairwise using `seam_flux_pointwise_cancel_conj` and `SeamVal`.
The pointwise estimate `crossDens_le` absorbs the cutoff cross term, yielding
`exists_energy_bound`. Finally `integrableOn_of_cutP_bound` passes to the
uncut density by Fatou's lemma. The argument thus uses seam cancellation,
not only an interior estimate on each disk.
-/
public import KsIndexLean.EnergySmooth
public import KsIndexLean.JacobiFields
public import KsIndexLean.PunctureGreen
public import KsIndexLean.PunctureCutoffP
public import KsIndexLean.SeamFlux
public import KsIndexLean.FirstGreen
public import KsIndexLean.CutoffLimit

@[expose] public section


open Complex Real MeasureTheory Filter Topology
open scoped ContDiff

noncomputable section

namespace KsIndex.FaithfulInjection

open KsIndex.Surface KsIndex.SurfaceForm KsIndex.JacobiFields KsIndex.PunctureCutoff
  KsIndex.PunctureGreen KsIndex.SeamNormal

variable {k m : ℕ}

/-! ### The flat Jacobi equation from `IsJacobiField` -/

/-- Reverse of `JacobiFields.laplacianG_add_absASq_of_flat`: on the open disk the geometric Jacobi
equation `Δ_g u + |A|²·u = 0` gives the flat equation `Δu + potV·u = 0`.  Uses `ρ_k > 0` on the
disk (the punctures, which carry `ρ_k = ∞`, miss the open disk) and `|A|²·ρ² = potV`
(`absA_sq_mul_rho_sq`). -/
lemma flat_of_laplacianG_add_absASq (hk : 2 ≤ k) {f : ℂ → ℂ} {w : ℂ} (hw : w ∈ disk)
    (h : laplacianG k f w + ((absA k w ^ 2 : ℝ) : ℂ) * f w = 0) :
    laplacian f w + (potV k w : ℂ) * f w = 0 := by
  have hnp : w ∉ punctures k := punctures_notMem_disk (by omega) hw
  have hρ : (0 : ℝ) < rho k w := rho_pos (by omega) hnp
  have hρ2 : (rho k w ^ 2 : ℝ) ≠ 0 := pow_ne_zero 2 hρ.ne'
  have hV : (absA k w ^ 2 : ℝ) = (rho k w ^ 2)⁻¹ * potV k w := by
    field_simp
    linear_combination absA_sq_mul_rho_sq hk hnp
  have key : laplacianG k f w + ((absA k w ^ 2 : ℝ) : ℂ) * f w
      = (((rho k w ^ 2)⁻¹ : ℝ) : ℂ) * (laplacian f w + (potV k w : ℂ) * f w) := by
    rw [laplacianG, hV]
    push_cast
    ring
  rw [key] at h
  have hinv : (((rho k w ^ 2)⁻¹ : ℝ) : ℂ) ≠ 0 := by
    simp only [ne_eq, Complex.ofReal_eq_zero, inv_eq_zero]; exact hρ2
  exact (mul_eq_zero.mp h).resolve_left hinv

/-- The per-copy flat Jacobi equation `Δ(u n) = −potV·(u n)` on the disk, from `IsJacobiField`.
This is the hypothesis shape consumed by the near-puncture removability toolkit
(`tested_identity_across_puncture` / `eps_identity`, with `V = potV k`). -/
lemma laplacian_eq_of_isJacobiField (hk : 2 ≤ k) {u : ZMod (2 * m) → ℂ → ℂ}
    (hjac : IsJacobiField k m u) (n : ZMod (2 * m)) {w : ℂ} (hw : w ∈ disk) :
    laplacian (u n) w = -((potV k w : ℂ) * u n w) :=
  eq_neg_of_add_eq_zero_left (flat_of_laplacianG_add_absASq hk hw (hjac n w hw))

/-! ### The finite-`L²` clause (free from boundedness) -/

/-- A bounded function continuous on the disk is `L²` there: `‖u n w‖² ≤ C²` on the finite-measure
disk.  The `EnergySmooth` `L²` clause for a `BoundedJacobi` member, with no Caccioppoli content. -/
lemma integrableOn_normSq_of_bounded {u : ZMod (2 * m) → ℂ → ℂ} (n : ZMod (2 * m))
    (hcont : ContinuousOn (u n) disk) {C : ℝ} (hC : ∀ w, ‖u n w‖ ≤ C) :
    IntegrableOn (fun w => ‖u n w‖ ^ 2) disk := by
  have hconst : IntegrableOn (fun _ : ℂ => C ^ 2) disk :=
    integrableOn_const measure_ball_lt_top.ne
  refine hconst.mono' ((hcont.norm.pow 2).aestronglyMeasurable measurableSet_disk) ?_
  refine ae_restrict_of_forall_mem measurableSet_disk fun w _ => ?_
  rw [Real.norm_of_nonneg (by positivity)]
  nlinarith [hC w, norm_nonneg (u n w)]

/-! ### Step (0) foundations: `u n` is `C^∞` up to the OPEN seam arcs (both sides) -/

/-- `σ = 1/·̄` is `C^∞` away from `0`. -/
lemma contDiffAt_sigma {w : ℂ} (hw : w ≠ 0) :
    ContDiffAt ℝ ∞ (fun z : ℂ => 1 / (starRingEnd ℂ) z) w := by
  have hcw : (starRingEnd ℂ) w ≠ 0 := by simpa using hw
  have hconj : ContDiffAt ℝ ∞ (fun z : ℂ => (starRingEnd ℂ) z) w :=
    Complex.conjCLE.contDiff.contDiffAt
  have hinv := hconj.inv hcw
  have hfun : (fun z : ℂ => 1 / (starRingEnd ℂ) z) = (fun z : ℂ => ((starRingEnd ℂ) z)⁻¹) := by
    funext z; rw [one_div]
  rw [hfun]; exact hinv

/-- **Giving-side germ.** Near a seam point of `seamArc k m n`, the giving copy `u n` agrees on
the disk with the smooth `glue u n`. -/
lemma eventuallyEq_glue_giving (hu : IsSmooth k m u) {n : ZMod (2 * m)} {w₀ : ℂ}
    (hw : w₀ ∈ seamArc k m n) :
    ContDiffAt ℝ ∞ (glue u n) w₀ ∧ u n =ᶠ[𝓝[disk] w₀] glue u n := by
  refine ⟨hu.2.1 n w₀ hw, ?_⟩
  filter_upwards [self_mem_nhdsWithin] with z hz
  have hz1 : ‖z‖ ≤ 1 := le_of_lt (mem_disk_iff.mp hz)
  simp only [glue, if_pos hz1]

/-- **Receiving-side germ.** Near a seam point of `seamArc k m n`, the receiving copy `u (n+1)`
agrees on the disk with the smooth reflection `glue u n ∘ σ`.  On the *open* disk this needs only
the involution `σ ∘ σ = id` — no boundary matching, hence no `SeamVal`: for `‖z‖ < 1` the reflected
point `σ z` has `‖σ z‖ > 1`, so `glue u n (σ z) = u (n+1) (σ (σ z)) = u (n+1) z`. -/
lemma eventuallyEq_glue_recv (hu : IsSmooth k m u) {n : ZMod (2 * m)} {w₀ : ℂ}
    (hw : w₀ ∈ seamArc k m n) :
    ContDiffAt ℝ ∞ ((glue u n) ∘ fun z : ℂ => 1 / (starRingEnd ℂ) z) w₀
      ∧ u (n + 1) =ᶠ[𝓝[disk] w₀] (glue u n) ∘ fun z : ℂ => 1 / (starRingEnd ℂ) z := by
  have hnorm : ‖w₀‖ = 1 := norm_eq_one_of_mem_seamArc hw
  have hw0 : w₀ ≠ 0 := fun h => by rw [h, norm_zero] at hnorm; norm_num at hnorm
  have hσw : (1 : ℂ) / (starRingEnd ℂ) w₀ = w₀ := sigma_fix_circle hnorm
  have hg : ContDiffAt ℝ ∞ (glue u n) ((fun z : ℂ => 1 / (starRingEnd ℂ) z) w₀) := by
    rw [show (fun z : ℂ => 1 / (starRingEnd ℂ) z) w₀ = w₀ from hσw]; exact hu.2.1 n w₀ hw
  refine ⟨hg.comp w₀ (contDiffAt_sigma hw0), ?_⟩
  have hhalf : {z : ℂ | (1 : ℝ) / 2 < ‖z‖} ∈ 𝓝[disk] w₀ := by
    refine nhdsWithin_le_nhds ((isOpen_lt continuous_const continuous_norm).mem_nhds ?_)
    change (1 : ℝ) / 2 < ‖w₀‖; rw [hnorm]; norm_num
  filter_upwards [self_mem_nhdsWithin, hhalf] with z hz hz2
  have hzlt : ‖z‖ < 1 := mem_disk_iff.mp hz
  have hz2' : (1 : ℝ) / 2 < ‖z‖ := hz2
  have hzpos : (0 : ℝ) < ‖z‖ := by linarith
  have hnormσ : ‖(1 : ℂ) / (starRingEnd ℂ) z‖ = ‖z‖⁻¹ := by
    rw [norm_div, norm_one, Complex.norm_conj, one_div]
  have hσgt : 1 < ‖(1 : ℂ) / (starRingEnd ℂ) z‖ := by
    rw [hnormσ]; exact (one_lt_inv₀ hzpos).mpr hzlt
  simp only [Function.comp_apply]
  unfold glue
  rw [if_neg (not_le.mpr hσgt), sigma_involutive z]

/-- Every non-puncture point of the closed disk carries a smooth germ agreeing with `u n` on the
disk: interior points use `u n` itself; boundary seam points use `glue u n` (giving) or
`glue u (n-1) ∘ σ` (receiving), dispatched by the arc-coverage of the circle minus punctures
(`mem_arc_of_not_puncture` + `parity_succ_val`). -/
lemma exists_germ_off_puncture (hu : IsSmooth k m u) (n : ZMod (2 * m)) {w₀ : ℂ}
    (hw₀ : ‖w₀‖ ≤ 1) (hp : w₀ ∉ punctures k) :
    ∃ F : ℂ → ℂ, ContDiffAt ℝ ∞ F w₀ ∧ u n =ᶠ[𝓝[disk] w₀] F := by
  rcases lt_or_eq_of_le hw₀ with hlt | heq
  · exact ⟨u n, (hu.1 n).contDiffAt (Metric.isOpen_ball.mem_nhds (mem_disk_iff.mpr hlt)),
      EventuallyEq.refl _ _⟩
  · have harc := mem_arc_of_not_puncture heq hp
    have hpv := parity_succ_val m n
    have hlt2 := ZMod.val_lt (parity m n)
    have hcases : w₀ ∈ seamArc k m n ∨ w₀ ∈ seamArc k m (n - 1) := by
      rw [seamArc_pred]; unfold seamArc; rw [hpv]
      rcases (by omega : (parity m n).val = 0 ∨ (parity m n).val = 1) with h | h <;>
        rcases harc with h0 | h1 <;> rw [h]
      · exact Or.inr h0
      · exact Or.inl h1
      · exact Or.inl h0
      · exact Or.inr h1
    rcases hcases with hA | hB
    · obtain ⟨hF, hee⟩ := eventuallyEq_glue_giving hu hA
      exact ⟨glue u n, hF, hee⟩
    · obtain ⟨hF, hee⟩ := eventuallyEq_glue_recv hu hB
      have hidx : (n - 1 + 1 : ZMod (2 * m)) = n := by ring
      rw [hidx] at hee
      exact ⟨(glue u (n - 1)) ∘ fun z : ℂ => 1 / (starRingEnd ℂ) z, hF, hee⟩

/-! ### Step (0): `gradSq (u n)` is bounded away from the punctures -/

/-- The flat gradient density of a germ that is `C^∞` at `w₀` is continuous at `w₀`. -/
lemma continuousAt_gradSq_of_contDiffAt {F : ℂ → ℂ} {w₀ : ℂ} (hF : ContDiffAt ℝ ∞ F w₀) :
    ContinuousAt (gradSq F) w₀ := by
  have hfd : ContinuousAt (fun w => fderiv ℝ F w) w₀ :=
    (hF.fderiv_right (m := 0) (by exact_mod_cast le_top)).continuousAt
  have h1 : ContinuousAt (fun w : ℂ => ‖fderiv ℝ F w 1‖ ^ 2) w₀ :=
    (hfd.clm_apply continuousAt_const).norm.pow 2
  have h2 : ContinuousAt (fun w : ℂ => ‖fderiv ℝ F w I‖ ^ 2) w₀ :=
    (hfd.clm_apply continuousAt_const).norm.pow 2
  exact h1.add h2

/-- **Local boundedness of `gradSq` from a germ.** If `g` agrees on the disk with a germ `F` that
is `C^∞` at `w₀`, then `gradSq g` is bounded by a constant on the disk near `w₀` (on an open
neighborhood `U`).  The equality `gradSq g = gradSq F` on the open set `U ∩ disk` comes from
`fderiv g = fderiv F` there (`EventuallyEq.fderiv_eq`, a full neighborhood of every interior
point). -/
lemma gradSq_locBdd_of_germ {g F : ℂ → ℂ} {w₀ : ℂ} (hF : ContDiffAt ℝ ∞ F w₀)
    (heq : g =ᶠ[𝓝[disk] w₀] F) :
    ∃ U : Set ℂ, IsOpen U ∧ w₀ ∈ U ∧ ∃ M : ℝ, ∀ w ∈ U, w ∈ disk → gradSq g w ≤ M := by
  have hcont : ContinuousAt (gradSq F) w₀ := continuousAt_gradSq_of_contDiffAt hF
  have hev : ∀ᶠ w in 𝓝 w₀, gradSq F w < gradSq F w₀ + 1 :=
    hcont.eventually (Iio_mem_nhds (lt_add_one (gradSq F w₀)))
  obtain ⟨W₀, hWimp, hWopen, hWmem⟩ := eventually_nhds_iff.mp hev
  have heq' : ∀ᶠ w in 𝓝 w₀, w ∈ disk → g w = F w := eventually_nhdsWithin_iff.mp heq
  obtain ⟨V₀, hVimp, hVopen, hVmem⟩ := eventually_nhds_iff.mp heq'
  refine ⟨V₀ ∩ W₀, hVopen.inter hWopen, ⟨hVmem, hWmem⟩, gradSq F w₀ + 1, ?_⟩
  intro w hwU hwdisk
  have hgF : g =ᶠ[𝓝 w] F := by
    filter_upwards [(hVopen.inter Metric.isOpen_ball).mem_nhds ⟨hwU.1, hwdisk⟩] with z hz
    exact hVimp z hz.1 hz.2
  have hval : gradSq g w = gradSq F w := by simp only [gradSq, hgF.fderiv_eq]
  rw [hval]
  exact le_of_lt (hWimp w hwU.2)

/-- **Step (0) a-priori bound.** `gradSq (u n)` is bounded on the part of the disk that stays
`δ`-away from every puncture — a compact set (closed subset of the closed disk) on which the germ
dispatch gives a local bound at every point; a finite subcover then gives the global bound. -/
lemma gradSq_bddAbove_of_disk_germs (hk : 1 ≤ k) {f : ℂ → ℂ}
    (hg : ∀ w : ℂ, ‖w‖ ≤ 1 → w ∉ punctures k →
      ∃ F : ℂ → ℂ, ContDiffAt ℝ ∞ F w ∧ f =ᶠ[𝓝[disk] w] F)
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ M : ℝ, ∀ w, w ∈ disk → (∀ p ∈ pF k, δ ≤ ‖w - p‖) → gradSq f w ≤ M := by
  classical
  have hSclosed : IsClosed {w : ℂ | ∀ p ∈ pF k, δ ≤ ‖w - p‖} := by
    have hSeq : {w : ℂ | ∀ p ∈ pF k, δ ≤ ‖w - p‖} = ⋂ p ∈ pF k, {w : ℂ | δ ≤ ‖w - p‖} :=
      Set.ext fun w => ⟨fun h => Set.mem_iInter₂.mpr h, fun h => Set.mem_iInter₂.mp h⟩
    rw [hSeq]
    exact isClosed_biInter fun p _ =>
      isClosed_le continuous_const (continuous_id.sub continuous_const).norm
  set K : Set ℂ := Metric.closedBall (0 : ℂ) 1 ∩ {w : ℂ | ∀ p ∈ pF k, δ ≤ ‖w - p‖} with hK
  have hKcompact : IsCompact K := (isCompact_closedBall 0 1).inter_right hSclosed
  have hloc : ∀ w₀ ∈ K, ∃ U : Set ℂ, IsOpen U ∧ w₀ ∈ U ∧
      ∃ M : ℝ, ∀ w ∈ U, w ∈ disk → gradSq f w ≤ M := by
    intro w₀ hw₀
    have hball : ‖w₀‖ ≤ 1 := by
      have := hw₀.1; rwa [Metric.mem_closedBall, dist_zero_right] at this
    have hnp : w₀ ∉ punctures k := by
      intro hpunc
      have hd := hw₀.2 w₀ ((mem_pF hk).mpr hpunc)
      rw [sub_self, norm_zero] at hd; linarith
    obtain ⟨F, hF, heq⟩ := hg w₀ hball hnp
    exact gradSq_locBdd_of_germ hF heq
  choose! U hUopen hUmem M hUbound using hloc
  obtain ⟨s, hs_sub, hs_cover⟩ :=
    hKcompact.elim_nhds_subcover U fun w₀ hw₀ => (hUopen w₀ hw₀).mem_nhds (hUmem w₀ hw₀)
  obtain ⟨Mg, hMg⟩ := (s.image M).finite_toSet.bddAbove
  refine ⟨Mg, fun w hwdisk hwaway => ?_⟩
  have hwK : w ∈ K := ⟨by
    rw [Metric.mem_closedBall, dist_zero_right]; exact le_of_lt (mem_disk_iff.mp hwdisk), hwaway⟩
  have hcov := hs_cover hwK
  rw [Set.mem_iUnion₂] at hcov
  obtain ⟨w₀, hw₀s, hwU⟩ := hcov
  have hw₀K : w₀ ∈ K := hs_sub w₀ hw₀s
  calc gradSq f w ≤ M w₀ := hUbound w₀ hw₀K w hwU hwdisk
    _ ≤ Mg := hMg (Finset.mem_coe.mpr (Finset.mem_image_of_mem M hw₀s))

/-- The chain version follows from its local disk germs. -/
lemma gradSq_bddAbove_off_punctures (hk : 1 ≤ k) (hu : IsSmooth k m u) (n : ZMod (2 * m))
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ M : ℝ, ∀ w, w ∈ disk → (∀ p ∈ pF k, δ ≤ ‖w - p‖) → gradSq (u n) w ≤ M :=
  gradSq_bddAbove_of_disk_germs hk (fun _ hw hp => exists_germ_off_puncture hu n hw hp) hδ

/-! ### Step (0) deliverable: the truncated Dirichlet integrand is integrable -/

/-- **Step (0).** For every cutoff scale `ε ∈ (0,1)`, the truncated Dirichlet integrand
`(cutP k ε)² · gradSq (u n)` is integrable on the disk.  This a-priori finiteness is what
legitimizes the Peter–Paul absorption in the Caccioppoli identity and feeds the Fatou step
(`integrableOn_of_cutP_bound`).  Proof: the integrand is `0` where `cutP = 0` (near the punctures)
and, where `cutP ≠ 0`, is `δ = ε²`-away from every puncture (so `gradSq (u n) ≤ M` by the a-priori
bound) with `cutP² ≤ 1`; either way it is dominated by a constant on the finite-measure disk. -/
lemma integrableOn_cutPSq_gradSq_of_disk_germs (hk : 2 ≤ k) {f : ℂ → ℂ}
    (hg : ∀ w : ℂ, ‖w‖ ≤ 1 → w ∉ punctures k →
      ∃ F : ℂ → ℂ, ContDiffAt ℝ ∞ F w ∧ f =ᶠ[𝓝[disk] w] F)
    {ε : ℝ} (h0 : 0 < ε) (h1 : ε < 1) :
    IntegrableOn (fun w => (cutP k ε w) ^ 2 * gradSq f w) disk := by
  obtain ⟨M, hM⟩ := gradSq_bddAbove_of_disk_germs (by omega) hg (δ := ε ^ 2) (by positivity)
  have hdom : ∀ w ∈ disk, (cutP k ε w) ^ 2 * gradSq f w ≤ max M 0 := by
    intro w hw
    by_cases hz : cutP k ε w = 0
    · rw [hz]
      have hzero : (0 : ℝ) ^ 2 * gradSq f w = 0 := by ring
      rw [hzero]; exact le_max_right M 0
    · have haway : ∀ p ∈ pF k, ε ^ 2 ≤ ‖w - p‖ := by
        intro p hp
        by_contra hlt
        rw [not_le] at hlt
        exact hz (cutP_eq_zero (by omega) h0 h1 ⟨p, (mem_pF (by omega)).mp hp, le_of_lt hlt⟩)
      calc (cutP k ε w) ^ 2 * gradSq f w
          ≤ 1 * gradSq f w :=
            mul_le_mul_of_nonneg_right (pow_le_one₀ (cutP_nonneg k ε w) (cutP_le_one k ε w))
              (gradSq_nonneg _ _)
        _ = gradSq f w := one_mul _
        _ ≤ M := hM w hw haway
        _ ≤ max M 0 := le_max_left M 0
  have hmeas : AEStronglyMeasurable (fun w => (cutP k ε w) ^ 2 * gradSq f w)
      (volume.restrict disk) :=
    (((cutP_contDiff k h0 h1).continuous.measurable.pow_const 2).mul
      (measurable_gradSq f)).aestronglyMeasurable
  have hconst : IntegrableOn (fun _ : ℂ => max M 0) disk :=
    integrableOn_const measure_ball_lt_top.ne
  refine hconst.mono' hmeas (ae_restrict_of_forall_mem measurableSet_disk fun w hw => ?_)
  rw [Real.norm_of_nonneg (mul_nonneg (sq_nonneg _) (gradSq_nonneg _ _))]
  exact hdom w hw

/-- The chain cutoff estimate is a specialization of the one-sided germ estimate. -/
lemma integrableOn_cutPSq_gradSq (hk : 2 ≤ k) (hu : IsSmooth k m u) (n : ZMod (2 * m))
    {ε : ℝ} (h0 : 0 < ε) (h1 : ε < 1) :
    IntegrableOn (fun w => (cutP k ε w) ^ 2 * gradSq (u n) w) disk :=
  integrableOn_cutPSq_gradSq_of_disk_germs hk
    (fun _ hw hp => exists_germ_off_puncture hu n hw hp) h0 h1

/-! ### The bounded potential and the test cutoff `(cutP)²·u` -/

/-- On the open disk the flat Jacobi potential is bounded by `8(k−1)²` (`‖w‖ < 1` makes
`‖w‖^{2k−4} ≤ 1` and `(‖w‖^{2k−2}+1)² ≥ 1`). -/
lemma potV_le_of_disk {w : ℂ} (hw : w ∈ disk) :
    potV k w ≤ 8 * ((k : ℝ) - 1) ^ 2 := by
  have hx : ‖w‖ < 1 := mem_disk_iff.mp hw
  have hx0 : (0 : ℝ) ≤ ‖w‖ := norm_nonneg w
  have hnum : ‖w‖ ^ (2 * k - 4) ≤ 1 := pow_le_one₀ hx0 (le_of_lt hx)
  have htpos : (0 : ℝ) ≤ ‖w‖ ^ (2 * k - 2) := pow_nonneg hx0 _
  have hden : (1 : ℝ) ≤ (‖w‖ ^ (2 * k - 2) + 1) ^ 2 := by nlinarith [htpos]
  have hcoef : (0 : ℝ) ≤ 8 * ((k : ℝ) - 1) ^ 2 := by positivity
  rw [potV, div_le_iff₀ (by positivity)]
  calc 8 * ((k : ℝ) - 1) ^ 2 * ‖w‖ ^ (2 * k - 4)
      ≤ 8 * ((k : ℝ) - 1) ^ 2 * 1 := by nlinarith [hcoef, hnum]
    _ ≤ 8 * ((k : ℝ) - 1) ^ 2 * (‖w‖ ^ (2 * k - 2) + 1) ^ 2 := by nlinarith [hcoef, hden]

/-- `(cutP k ε)²` as a smooth `ℂ`-valued function. -/
lemma contDiff_cutPSqC (k : ℕ) {ε : ℝ} (h0 : 0 < ε) (h1 : ε < 1) :
    ContDiff ℝ ∞ (fun z : ℂ => ((cutP k ε z) ^ 2 : ℂ)) :=
  (Complex.ofRealCLM.contDiff.comp (cutP_contDiff k h0 h1)).pow 2

lemma differentiableAt_cutPSqC (k : ℕ) {ε : ℝ} (h0 : 0 < ε) (h1 : ε < 1) (w : ℂ) :
    DifferentiableAt ℝ (fun z : ℂ => ((cutP k ε z) ^ 2 : ℂ)) w :=
  (contDiff_cutPSqC k h0 h1).differentiable (by simp) w

/-- The derivative of `(cutP)²` (as `ℂ`) is `2·cutP·(derivative of cutPC)` — the chain factor that
ties the test-cutoff cross term to the cutoff energy `∫|∇ cutP|²`. -/
lemma fderiv_cutPSqC (k : ℕ) {ε : ℝ} (h0 : 0 < ε) (h1 : ε < 1) (w e : ℂ) :
    fderiv ℝ (fun z : ℂ => ((cutP k ε z) ^ 2 : ℂ)) w e
      = 2 * (cutP k ε w : ℂ) * fderiv ℝ (cutPC k ε) w e := by
  have hc : HasFDerivAt (cutPC k ε) (fderiv ℝ (cutPC k ε) w) w :=
    ((Complex.ofRealCLM.contDiff.comp (cutP_contDiff k h0 h1)).differentiable
      (by simp) w).hasFDerivAt
  have hsq : HasFDerivAt (fun z : ℂ => ((cutP k ε z) ^ 2 : ℂ))
      ((2 * (cutP k ε w : ℂ)) • fderiv ℝ (cutPC k ε) w) w := by
    have := hc.pow 2
    simpa [cutPC, pow_one, two_mul, mul_comm, mul_assoc] using this
  rw [hsq.fderiv]
  simp [mul_assoc]

/-- **Pointwise gradient expansion of the test function.**  With `v = (cutP)²·u`,
`⟨∇u, ∇v⟩ = (cutP)²·|∇u|²  +  u·(conj(∂u)·∂(cutP)²)`.  The first term is the truncated energy
density; the second is the cutoff cross term controlled by `∫|∇ cutP|²`. -/
lemma gradInner_testV_expand {k : ℕ} {ε : ℝ} (h0 : 0 < ε) (h1 : ε < 1)
    {u : ZMod (2 * m) → ℂ → ℂ} (n : ZMod (2 * m)) {w : ℂ}
    (hdu : DifferentiableAt ℝ (u n) w) :
    KsIndex.GradOrtho.gradInner (u n) (fun z => ((cutP k ε z) ^ 2 : ℂ) * u n z) w
      = ((cutP k ε w) ^ 2 : ℂ) * (gradSq (u n) w : ℂ)
        + u n w * ((starRingEnd ℂ) (fderiv ℝ (u n) w 1)
              * fderiv ℝ (fun z => ((cutP k ε z) ^ 2 : ℂ)) w 1
            + (starRingEnd ℂ) (fderiv ℝ (u n) w I)
              * fderiv ℝ (fun z => ((cutP k ε z) ^ 2 : ℂ)) w I) := by
  have hgχ := differentiableAt_cutPSqC k h0 h1 w
  have hv : HasFDerivAt (fun z => ((cutP k ε z) ^ 2 : ℂ) * u n z)
      (((cutP k ε w) ^ 2 : ℂ) • fderiv ℝ (u n) w
        + u n w • fderiv ℝ (fun z => ((cutP k ε z) ^ 2 : ℂ)) w) w :=
    hgχ.hasFDerivAt.mul hdu.hasFDerivAt
  rw [KsIndex.GradOrtho.gradInner, hv.fderiv, Surface.gradSq]
  simp only [add_apply, smul_apply, smul_eq_mul]
  set a1 := fderiv ℝ (u n) w 1 with ha1
  set aI := fderiv ℝ (u n) w I with haI
  have e1 : (starRingEnd ℂ) a1 * a1 = (‖a1‖ : ℂ) ^ 2 := by
    rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq]; push_cast; ring
  have eI : (starRingEnd ℂ) aI * aI = (‖aI‖ : ℂ) ^ 2 := by
    rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq]; push_cast; ring
  push_cast
  linear_combination (((cutP k ε w) ^ 2 : ℂ)) * e1 + (((cutP k ε w) ^ 2 : ℂ)) * eI

/-- **Pointwise potential term.**  `conj(Δu)·((cutP)²·u) = −potV·(cutP)²·‖u‖²`, using the flat
Jacobi equation `Δu = −potV·u`. -/
lemma conj_lap_testV (hk : 2 ≤ k) {u : ZMod (2 * m) → ℂ → ℂ}
    (hjac : IsJacobiField k m u) (n : ZMod (2 * m)) {w : ℂ} (hw : w ∈ disk) {ε : ℝ} :
    (starRingEnd ℂ) (laplacian (u n) w) * (((cutP k ε w) ^ 2 : ℂ) * u n w)
      = -((potV k w * (cutP k ε w) ^ 2 * ‖u n w‖ ^ 2 : ℝ) : ℂ) := by
  rw [laplacian_eq_of_isJacobiField hk hjac n hw]
  have huu : (starRingEnd ℂ) (u n w) * u n w = (‖u n w‖ : ℂ) ^ 2 := by
    rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq]; push_cast; ring
  simp only [map_neg, map_mul, Complex.conj_ofReal]
  push_cast
  linear_combination (-((potV k w : ℂ) * ((cutP k ε w) ^ 2 : ℂ))) * huu

/-! ### Interior second-order differentiability -/

/-- A `C^∞` germ has a differentiable first derivative in every fixed direction — the `hu2x`/`hu2y`
shape `first_green_disk` consumes. -/
lemma differentiableAt_fderiv_dir {F : ℂ → ℂ} {w : ℂ} (hF : ContDiffAt ℝ ∞ F w) (d : ℂ) :
    DifferentiableAt ℝ (fun z => fderiv ℝ F z d) w :=
  ((hF.fderiv_right (m := 1)
    (by simpa using (WithTop.coe_le_coe.mpr (le_top : (1 + 1 : ℕ∞) ≤ ⊤)))).clm_apply
      contDiffAt_const).differentiableAt one_ne_zero

/-! ### The boundary-trace germ: a smooth representative on the closed disk -/

/-- **Closed-disk germ off the punctures.**  At a non-puncture boundary point, `u n` agrees with a
`C^∞` germ `F` on an *open* neighborhood intersected with the closed disk — the strengthening of
`exists_germ_off_puncture` from `𝓝[disk]` (interior only) to the closed disk, which the
`fderivWithin (closedBall)` trace needs.  Giving arcs use `glue u n` (equal to `u n` on the whole
closed disk); receiving arcs use the reflected germ `glue u (n-1) ∘ σ`, whose circle values match
`u n` by `SeamVal`. -/
lemma exists_germ_closedBall (hu : IsSmooth k m u) (hsv : SeamVal k u) (n : ZMod (2 * m)) {w₀ : ℂ}
    (hw₀ : ‖w₀‖ = 1) (hp : w₀ ∉ punctures k) :
    ∃ F : ℂ → ℂ, ContDiffAt ℝ ∞ F w₀ ∧ ∃ W : Set ℂ, IsOpen W ∧ w₀ ∈ W ∧
      ∀ z ∈ W, ‖z‖ ≤ 1 → u n z = F z := by
  have harc := mem_arc_of_not_puncture hw₀ hp
  have hpv := parity_succ_val m n
  have hlt2 := ZMod.val_lt (parity m n)
  have hcases : w₀ ∈ seamArc k m n ∨ w₀ ∈ seamArc k m (n - 1) := by
    rw [seamArc_pred]; unfold seamArc; rw [hpv]
    rcases (by omega : (parity m n).val = 0 ∨ (parity m n).val = 1) with h | h <;>
      rcases harc with h0 | h1 <;> rw [h]
    · exact Or.inr h0
    · exact Or.inl h1
    · exact Or.inl h0
    · exact Or.inr h1
  rcases hcases with hA | hB
  · -- giving arc: `glue u n = u n` on the whole closed disk
    refine ⟨glue u n, (eventuallyEq_glue_giving hu hA).1, Set.univ, isOpen_univ, Set.mem_univ _,
      fun z _ hz1 => ?_⟩
    simp only [glue, if_pos hz1]
  · -- receiving arc: the reflected germ, matched on the circle by `SeamVal`
    obtain ⟨hFc, hee⟩ := eventuallyEq_glue_recv (n := n - 1) hu hB
    have hidx : (n - 1 + 1 : ZMod (2 * m)) = n := by ring
    rw [hidx] at hee
    obtain ⟨V₀, hV₀eq, hV₀open, hV₀mem⟩ := eventually_nhds_iff.mp (eventually_nhdsWithin_iff.mp hee)
    set p : ℕ := (parity m n).val with hp'
    have hwArc : (-1 : ℝ) ^ p * (w₀ ^ k).re < 0 := by
      rw [seamArc_pred] at hB; exact hB.2
    refine ⟨(glue u (n - 1)) ∘ fun z : ℂ => 1 / (starRingEnd ℂ) z, hFc,
      V₀ ∩ {z : ℂ | (-1 : ℝ) ^ p * (z ^ k).re < 0},
      hV₀open.inter (isOpen_lt (by fun_prop) continuous_const), ⟨hV₀mem, hwArc⟩, ?_⟩
    rintro z ⟨hzV₀, hzArc⟩ hz1
    rcases lt_or_eq_of_le hz1 with hlt | heq1
    · exact hV₀eq z hzV₀ (mem_disk_iff.mpr hlt)
    · have hz_norm : ‖z‖ = 1 := heq1
      have hz_arc : z ∈ seamArc k m (n - 1) := by
        rw [seamArc_pred]; exact ⟨hz_norm, hzArc⟩
      have hσz : (1 : ℂ) / (starRingEnd ℂ) z = z := sigma_fix_circle hz_norm
      have hFz : ((glue u (n - 1)) ∘ fun z : ℂ => 1 / (starRingEnd ℂ) z) z = u (n - 1) z := by
        simp only [Function.comp_apply, hσz, glue, if_pos (le_of_eq hz_norm)]
      have hsvz : u (n - 1 + 1) z = u (n - 1) z := hsv (n - 1) z hz_arc
      rw [hidx] at hsvz
      rw [hFz]; exact hsvz

/-! ### Continuity of the boundary flux up to the closed disk -/

/-- `UniqueDiffWithinAt` holds at every point of the closed unit disk. -/
lemma uniqueDiffWithinAt_closedBall {z : ℂ} (hz : z ∈ Metric.closedBall (0 : ℂ) 1) :
    UniqueDiffWithinAt ℝ (Metric.closedBall (0 : ℂ) 1) z :=
  uniqueDiffOn_convex (convex_closedBall 0 1)
    (by rw [interior_closedBall _ (by norm_num : (1 : ℝ) ≠ 0)]
        exact ⟨0, Metric.mem_ball_self (by norm_num)⟩) z hz

/-- **The boundary flux is continuous up to the closed disk.**  For `v = (cutP)²·u`, the flux
`conj(∂_e^within u)·v` is continuous on `closedBall 0 1` — the `hFxc`/`hFyc` hypothesis of
`first_green_disk`.  Interior points use `fderivWithin = fderiv` and smoothness; punctures use
`cutP = 0` nearby (the flux is locally `0`); other boundary points use the smooth closed-disk germ
of `exists_germ_closedBall`. -/
lemma continuousOn_flux_of_disk_germs (hk : 1 ≤ k) {f : ℂ → ℂ}
    (hsm : ContDiffOn ℝ ∞ f disk)
    (hg : ∀ w : ℂ, ‖w‖ = 1 → w ∉ punctures k →
      ∃ F : ℂ → ℂ, ContDiffAt ℝ ∞ F w ∧
        ∀ᶠ z in 𝓝 w, ‖z‖ ≤ 1 → f z = F z)
    (e : ℂ) {ε : ℝ} (h0 : 0 < ε) (h1 : ε < 1) :
    ContinuousOn (fun w => (starRingEnd ℂ) (fderivWithin ℝ f (Metric.closedBall 0 1) w e)
        * (((cutP k ε w) ^ 2 : ℂ) * f w)) (Metric.closedBall 0 1) := by
  intro w₀ hw₀
  have hn0 : ‖w₀‖ ≤ 1 := by rwa [Metric.mem_closedBall, dist_zero_right] at hw₀
  have hcont_cutP2 : ContinuousAt (fun w => ((cutP k ε w) ^ 2 : ℂ)) w₀ :=
    ((Complex.continuous_ofReal.comp (cutP_contDiff k h0 h1).continuous).pow 2).continuousAt
  rcases lt_or_eq_of_le hn0 with hlt | heq
  · -- interior point: `fderivWithin = fderiv`, everything smooth
    have hwdisk : w₀ ∈ disk := mem_disk_iff.mpr hlt
    have hcdu : ContDiffAt ℝ ∞ f w₀ := hsm.contDiffAt (Metric.isOpen_ball.mem_nhds hwdisk)
    have hEq : (fun w => (starRingEnd ℂ) (fderivWithin ℝ f (Metric.closedBall 0 1) w e)
          * (((cutP k ε w) ^ 2 : ℂ) * f w))
        =ᶠ[𝓝 w₀] (fun w => (starRingEnd ℂ) (fderiv ℝ f w e)
          * (((cutP k ε w) ^ 2 : ℂ) * f w)) := by
      filter_upwards [Metric.isOpen_ball.mem_nhds hwdisk] with z hz
      rw [fderivWithin_of_mem_nhds
        (Filter.mem_of_superset (Metric.isOpen_ball.mem_nhds hz) Metric.ball_subset_closedBall)]
    have hfd : ContinuousAt (fun w => fderiv ℝ f w e) w₀ :=
      ((hcdu.fderiv_right (m := 0) (by exact_mod_cast le_top)).continuousAt).clm_apply
        continuousAt_const
    have hcont : ContinuousAt (fun w => (starRingEnd ℂ) (fderiv ℝ f w e)
        * (((cutP k ε w) ^ 2 : ℂ) * f w)) w₀ :=
      ((Complex.continuous_conj.continuousAt).comp hfd).mul
        (hcont_cutP2.mul hcdu.continuousAt)
    exact ((hcont.congr hEq.symm).continuousWithinAt)
  · -- boundary point
    by_cases hpunc : w₀ ∈ punctures k
    · -- puncture: `cutP = 0` nearby, so the flux vanishes on a neighborhood
      have hF0 : (fun w => (starRingEnd ℂ) (fderivWithin ℝ f (Metric.closedBall 0 1) w e)
            * (((cutP k ε w) ^ 2 : ℂ) * f w)) =ᶠ[𝓝 w₀] (fun _ => (0 : ℂ)) := by
        filter_upwards [Metric.ball_mem_nhds w₀ (by positivity : (0 : ℝ) < ε ^ 2)] with z hz
        have hzc : cutP k ε z = 0 :=
          cutP_eq_zero hk h0 h1 ⟨w₀, hpunc,
            le_of_lt (by rwa [Metric.mem_ball, dist_eq_norm] at hz)⟩
        simp [hzc]
      exact (continuousAt_const.congr hF0.symm).continuousWithinAt
    · -- other boundary point: the smooth closed-disk germ
      obtain ⟨F, hFc, hs⟩ := hg w₀ heq hpunc
      obtain ⟨W, hWeq, hWopen, hwW⟩ := eventually_nhds_iff.mp hs
      have hev : ∀ᶠ z in 𝓝 w₀, DifferentiableAt ℝ F z := by
        filter_upwards [(hFc.of_le two_le_infty).eventually (by simp)] with z hz
          using hz.differentiableAt (by norm_num)
      obtain ⟨V, hVsub, hVopen, hVmem⟩ := eventually_nhds_iff.mp hev
      have hfdF : ContinuousAt (fun w => fderiv ℝ F w e) w₀ :=
        ((hFc.fderiv_right (m := 0) (by exact_mod_cast le_top)).continuousAt).clm_apply
          continuousAt_const
      -- the RHS germ-flux is continuous at `w₀`
      have hRHS : ContinuousAt (fun w => (starRingEnd ℂ) (fderiv ℝ F w e)
          * (((cutP k ε w) ^ 2 : ℂ) * F w)) w₀ :=
        ((Complex.continuous_conj.continuousAt).comp hfdF).mul
          (hcont_cutP2.mul (hFc.continuousAt))
      -- the flux agrees with the germ-flux near `w₀` within the closed disk
      refine (hRHS.continuousWithinAt).congr_of_eventuallyEq
        (eventually_nhdsWithin_iff.mpr ?_) ?_
      · filter_upwards [(hWopen.inter hVopen).mem_nhds ⟨hwW, hVmem⟩] with z hz hzcb
        obtain ⟨hzW, hzV⟩ := hz
        have hz1 : ‖z‖ ≤ 1 := by rwa [Metric.mem_closedBall, dist_zero_right] at hzcb
        have huF : f z = F z := hWeq z hzW hz1
        have hfdw : fderivWithin ℝ f (Metric.closedBall 0 1) z e
            = fderiv ℝ F z e := by
          have hcongr : f =ᶠ[𝓝[Metric.closedBall (0 : ℂ) 1] z] F := by
            refine eventually_nhdsWithin_iff.mpr ?_
            filter_upwards [hWopen.mem_nhds hzW] with y hy hycb
            exact hWeq y hy (by rwa [Metric.mem_closedBall, dist_zero_right] at hycb)
          rw [hcongr.fderivWithin_eq huF,
            (hVsub z hzV).hasFDerivAt.hasFDerivWithinAt.fderivWithin
              (uniqueDiffWithinAt_closedBall hzcb)]
        rw [hfdw, huF]
      · have hfdw₀ : fderivWithin ℝ f (Metric.closedBall 0 1) w₀ e = fderiv ℝ F w₀ e := by
          have hcongr : f =ᶠ[𝓝[Metric.closedBall (0 : ℂ) 1] w₀] F := by
            refine eventually_nhdsWithin_iff.mpr ?_
            filter_upwards [hWopen.mem_nhds hwW] with y hy hycb
            exact hWeq y hy (by rwa [Metric.mem_closedBall, dist_zero_right] at hycb)
          rw [hcongr.fderivWithin_eq (hWeq w₀ hwW hn0),
            (hVsub w₀ hVmem).hasFDerivAt.hasFDerivWithinAt.fderivWithin
              (uniqueDiffWithinAt_closedBall hw₀)]
        rw [hfdw₀, hWeq w₀ hwW hn0]

/-- Chain fields supply the one-sided closed-disk germs used by the flux estimate. -/
lemma continuousOn_flux (hk : 1 ≤ k) (hu : IsSmooth k m u) (hsv : SeamVal k u) (n : ZMod (2 * m))
    (e : ℂ) {ε : ℝ} (h0 : 0 < ε) (h1 : ε < 1) :
    ContinuousOn (fun w => (starRingEnd ℂ) (fderivWithin ℝ (u n) (Metric.closedBall 0 1) w e)
        * (((cutP k ε w) ^ 2 : ℂ) * u n w)) (Metric.closedBall 0 1) := by
  apply continuousOn_flux_of_disk_germs hk (hu.1 n) ?_ e h0 h1
  intro w hw hp
  obtain ⟨F, hF, U, hU, hwU, he⟩ := exists_germ_closedBall hu hsv n hw hp
  exact ⟨F, hF, Filter.eventually_of_mem (hU.mem_nhds hwU) he⟩

/-- **The radial boundary flux is continuous up to the closed disk** — the diagonal variant of
`continuousOn_flux` with direction equal to the point itself (the normal trace `∂_ν`), needed for
the boundary θ-integral's integrability. -/
lemma continuousOn_flux_diag (hk : 1 ≤ k) (hu : IsSmooth k m u) (hsv : SeamVal k u)
    (n : ZMod (2 * m)) {ε : ℝ} (h0 : 0 < ε) (h1 : ε < 1) :
    ContinuousOn (fun w => (starRingEnd ℂ) (fderivWithin ℝ (u n) (Metric.closedBall 0 1) w w)
        * (((cutP k ε w) ^ 2 : ℂ) * u n w)) (Metric.closedBall 0 1) := by
  intro w₀ hw₀
  have hn0 : ‖w₀‖ ≤ 1 := by rwa [Metric.mem_closedBall, dist_zero_right] at hw₀
  have hcont_cutP2 : ContinuousAt (fun w => ((cutP k ε w) ^ 2 : ℂ)) w₀ :=
    ((Complex.continuous_ofReal.comp (cutP_contDiff k h0 h1).continuous).pow 2).continuousAt
  rcases lt_or_eq_of_le hn0 with hlt | heq
  · have hwdisk : w₀ ∈ disk := mem_disk_iff.mpr hlt
    have hcdu : ContDiffAt ℝ ∞ (u n) w₀ := (hu.1 n).contDiffAt (Metric.isOpen_ball.mem_nhds hwdisk)
    have hEq : (fun w => (starRingEnd ℂ) (fderivWithin ℝ (u n) (Metric.closedBall 0 1) w w)
          * (((cutP k ε w) ^ 2 : ℂ) * u n w))
        =ᶠ[𝓝 w₀] (fun w => (starRingEnd ℂ) (fderiv ℝ (u n) w w)
          * (((cutP k ε w) ^ 2 : ℂ) * u n w)) := by
      filter_upwards [Metric.isOpen_ball.mem_nhds hwdisk] with z hz
      rw [fderivWithin_of_mem_nhds
        (Filter.mem_of_superset (Metric.isOpen_ball.mem_nhds hz) Metric.ball_subset_closedBall)]
    have hfd : ContinuousAt (fun w => fderiv ℝ (u n) w w) w₀ :=
      ((hcdu.fderiv_right (m := 0) (by exact_mod_cast le_top)).continuousAt).clm_apply
        continuousAt_id
    have hcont : ContinuousAt (fun w => (starRingEnd ℂ) (fderiv ℝ (u n) w w)
        * (((cutP k ε w) ^ 2 : ℂ) * u n w)) w₀ :=
      ((Complex.continuous_conj.continuousAt).comp hfd).mul (hcont_cutP2.mul hcdu.continuousAt)
    exact ((hcont.congr hEq.symm).continuousWithinAt)
  · by_cases hpunc : w₀ ∈ punctures k
    · have hF0 : (fun w => (starRingEnd ℂ) (fderivWithin ℝ (u n) (Metric.closedBall 0 1) w w)
            * (((cutP k ε w) ^ 2 : ℂ) * u n w)) =ᶠ[𝓝 w₀] (fun _ => (0 : ℂ)) := by
        filter_upwards [Metric.ball_mem_nhds w₀ (by positivity : (0 : ℝ) < ε ^ 2)] with z hz
        have hzc : cutP k ε z = 0 :=
          cutP_eq_zero hk h0 h1 ⟨w₀, hpunc,
            le_of_lt (by rwa [Metric.mem_ball, dist_eq_norm] at hz)⟩
        simp [hzc]
      exact (continuousAt_const.congr hF0.symm).continuousWithinAt
    · obtain ⟨F, hFc, W, hWopen, hwW, hWeq⟩ := exists_germ_closedBall hu hsv n heq hpunc
      have hev : ∀ᶠ z in 𝓝 w₀, DifferentiableAt ℝ F z := by
        filter_upwards [(hFc.of_le two_le_infty).eventually (by simp)] with z hz
          using hz.differentiableAt (by norm_num)
      obtain ⟨V, hVsub, hVopen, hVmem⟩ := eventually_nhds_iff.mp hev
      have hfdF : ContinuousAt (fun w => fderiv ℝ F w w) w₀ :=
        ((hFc.fderiv_right (m := 0) (by exact_mod_cast le_top)).continuousAt).clm_apply
          continuousAt_id
      have hRHS : ContinuousAt (fun w => (starRingEnd ℂ) (fderiv ℝ F w w)
          * (((cutP k ε w) ^ 2 : ℂ) * F w)) w₀ :=
        ((Complex.continuous_conj.continuousAt).comp hfdF).mul (hcont_cutP2.mul (hFc.continuousAt))
      refine (hRHS.continuousWithinAt).congr_of_eventuallyEq
        (eventually_nhdsWithin_iff.mpr ?_) ?_
      · filter_upwards [(hWopen.inter hVopen).mem_nhds ⟨hwW, hVmem⟩] with z hz hzcb
        obtain ⟨hzW, hzV⟩ := hz
        have hz1 : ‖z‖ ≤ 1 := by rwa [Metric.mem_closedBall, dist_zero_right] at hzcb
        have huF : u n z = F z := hWeq z hzW hz1
        have hfdw : fderivWithin ℝ (u n) (Metric.closedBall 0 1) z z = fderiv ℝ F z z := by
          have hcongr : u n =ᶠ[𝓝[Metric.closedBall (0 : ℂ) 1] z] F := by
            refine eventually_nhdsWithin_iff.mpr ?_
            filter_upwards [hWopen.mem_nhds hzW] with y hy hycb
            exact hWeq y hy (by rwa [Metric.mem_closedBall, dist_zero_right] at hycb)
          rw [hcongr.fderivWithin_eq huF,
            (hVsub z hzV).hasFDerivAt.hasFDerivWithinAt.fderivWithin
              (uniqueDiffWithinAt_closedBall hzcb)]
        rw [hfdw, huF]
      · have hfdw₀ : fderivWithin ℝ (u n) (Metric.closedBall 0 1) w₀ w₀ = fderiv ℝ F w₀ w₀ := by
          have hcongr : u n =ᶠ[𝓝[Metric.closedBall (0 : ℂ) 1] w₀] F := by
            refine eventually_nhdsWithin_iff.mpr ?_
            filter_upwards [hWopen.mem_nhds hwW] with y hy hycb
            exact hWeq y hy (by rwa [Metric.mem_closedBall, dist_zero_right] at hycb)
          rw [hcongr.fderivWithin_eq (hWeq w₀ hwW hn0),
            (hVsub w₀ hVmem).hasFDerivAt.hasFDerivWithinAt.fderivWithin
              (uniqueDiffWithinAt_closedBall hw₀)]
        rw [hfdw₀, hWeq w₀ hwW hn0]

/-! ### Integrability of the three pieces of the Green integrand -/

/-- The flat Jacobi potential is continuous (its denominator `(‖w‖^{2k−2}+1)²` never vanishes). -/
lemma continuous_potV (k : ℕ) : Continuous (potV k) := by
  unfold potV
  apply Continuous.div (by fun_prop) (by fun_prop)
  intro w; positivity

/-- **The truncated energy density** `(cutP)²·|∇u|²` (as `ℂ`) is integrable on the disk — the
`ℂ`-coercion of the step-(0) real integrability. -/
lemma integrableOn_energyTestC (hk : 2 ≤ k) (hu : IsSmooth k m u) (n : ZMod (2 * m)) {ε : ℝ}
    (h0 : 0 < ε) (h1 : ε < 1) :
    IntegrableOn (fun w => ((cutP k ε w) ^ 2 : ℂ) * (gradSq (u n) w : ℂ)) disk := by
  have hr : IntegrableOn (fun w => (cutP k ε w) ^ 2 * gradSq (u n) w) disk :=
    integrableOn_cutPSq_gradSq hk hu n h0 h1
  have hc : IntegrableOn (fun w => (((cutP k ε w) ^ 2 * gradSq (u n) w : ℝ) : ℂ)) disk := hr.ofReal
  refine hc.congr_fun (fun w _ => ?_) measurableSet_disk
  push_cast; ring

/-- **The potential density** `potV·(cutP)²·‖u‖²` is integrable on the disk — bounded by
`8(k−1)²·C²` on the finite-measure disk. -/
lemma integrableOn_potTestReal_of_disk (k : ℕ) {f : ℂ → ℂ}
    (hsm : ContDiffOn ℝ ∞ f disk) {ε : ℝ}
    (h0 : 0 < ε) (h1 : ε < 1) {C : ℝ} (hC : ∀ w ∈ disk, ‖f w‖ ≤ C) :
    IntegrableOn (fun w => potV k w * (cutP k ε w) ^ 2 * ‖f w‖ ^ 2) disk := by
  have hmeas : AEStronglyMeasurable
      (fun w => potV k w * (cutP k ε w) ^ 2 * ‖f w‖ ^ 2) (volume.restrict disk) :=
    (((continuous_potV k).continuousOn.mul
      (((cutP_contDiff k h0 h1).continuous.pow 2).continuousOn)).mul
        (hsm.continuousOn.norm.pow 2)).aestronglyMeasurable measurableSet_disk
  have hconst : IntegrableOn (fun _ : ℂ => 8 * ((k : ℝ) - 1) ^ 2 * C ^ 2) disk :=
    integrableOn_const measure_ball_lt_top.ne
  refine hconst.mono' hmeas (ae_restrict_of_forall_mem measurableSet_disk fun w hw => ?_)
  have hpotnn : 0 ≤ potV k w := by unfold potV; positivity
  rw [Real.norm_of_nonneg (mul_nonneg (mul_nonneg hpotnn (sq_nonneg _)) (sq_nonneg _))]
  have h1' : potV k w ≤ 8 * ((k : ℝ) - 1) ^ 2 := potV_le_of_disk hw
  have h2' : (cutP k ε w) ^ 2 ≤ 1 := by nlinarith [cutP_nonneg k ε w, cutP_le_one k ε w]
  have h3' : ‖f w‖ ^ 2 ≤ C ^ 2 := by nlinarith [hC w hw, norm_nonneg (f w)]
  have hpc : potV k w * (cutP k ε w) ^ 2 ≤ 8 * ((k : ℝ) - 1) ^ 2 :=
    le_of_le_of_eq (mul_le_mul h1' h2' (sq_nonneg _) (by positivity)) (mul_one _)
  exact mul_le_mul hpc h3' (sq_nonneg _) (by positivity)

lemma integrableOn_potTestReal (hu : IsSmooth k m u) (n : ZMod (2 * m)) {ε : ℝ}
    (h0 : 0 < ε) (h1 : ε < 1) {C : ℝ} (hC : ∀ w, ‖u n w‖ ≤ C) :
    IntegrableOn (fun w => potV k w * (cutP k ε w) ^ 2 * ‖u n w‖ ^ 2) disk :=
  integrableOn_potTestReal_of_disk k (hu.1 n) h0 h1 (fun w _ => hC w)

/-- The cutoff cross density `u·(conj(∂u)·∂(cutP)²)` — the non-energy part of the pairing. -/
def crossDens (k : ℕ) (ε : ℝ) (f : ℂ → ℂ) (w : ℂ) : ℂ :=
  f w * ((starRingEnd ℂ) (fderiv ℝ f w 1) * fderiv ℝ (fun z => ((cutP k ε z) ^ 2 : ℂ)) w 1
    + (starRingEnd ℂ) (fderiv ℝ f w I) * fderiv ℝ (fun z => ((cutP k ε z) ^ 2 : ℂ)) w I)

/-- The cutoff's own gradient density is continuous. -/
lemma continuous_gradSq_cutPC (k : ℕ) {ε : ℝ} (h0 : 0 < ε) (h1 : ε < 1) :
    Continuous (gradSq (cutPC k ε)) := by
  have hfd : Continuous (fun w => fderiv ℝ (cutPC k ε) w) :=
    (Complex.ofRealCLM.contDiff.comp (cutP_contDiff k h0 h1)).continuous_fderiv
      (by simp)
  unfold gradSq
  exact ((hfd.clm_apply continuous_const).norm.pow 2).add
    ((hfd.clm_apply continuous_const).norm.pow 2)

/-- Continuity of a fixed directional derivative of `u n` on the open disk. -/
lemma continuousOn_fderivDir_of_disk {f : ℂ → ℂ}
    (hsm : ContDiffOn ℝ ∞ f disk) (e : ℂ) :
    ContinuousOn (fun w => fderiv ℝ f w e) (Metric.ball 0 1) := fun w hw =>
  ((((hsm.contDiffAt (Metric.isOpen_ball.mem_nhds hw)).fderiv_right (m := 0)
    (by exact_mod_cast le_top)).continuousAt).clm_apply continuousAt_const).continuousWithinAt

lemma continuousOn_fderivDir_ball (hu : IsSmooth k m u) (n : ZMod (2 * m)) (e : ℂ) :
    ContinuousOn (fun w => fderiv ℝ (u n) w e) (Metric.ball 0 1) :=
  continuousOn_fderivDir_of_disk (hu.1 n) e

/-- **The cutoff cross density is integrable** on the disk.  Extracting the chain factor
`∂(cutP)² = 2·cutP·∂cutP`, the density is `2·cutP·u·⟨∇u, ∇cutP⟩`; where `cutP ≠ 0` the point is
`ε²`-away from every puncture (so `|∇u|² ≤ M`) and elsewhere the density vanishes, so it is bounded
by `C·(M + Mχ)` on the finite-measure disk (`Mχ` a bound for `|∇cutP|²`). -/
lemma integrableOn_crossDens_of_disk_germs (hk : 2 ≤ k) {f : ℂ → ℂ}
    (hsm : ContDiffOn ℝ ∞ f disk)
    (hg : ∀ w : ℂ, ‖w‖ ≤ 1 → w ∉ punctures k →
      ∃ F : ℂ → ℂ, ContDiffAt ℝ ∞ F w ∧ f =ᶠ[𝓝[disk] w] F)
    {ε : ℝ} (h0 : 0 < ε) (h1 : ε < 1) {C : ℝ} (hC : ∀ w ∈ disk, ‖f w‖ ≤ C) :
    IntegrableOn (crossDens k ε f) disk := by
  obtain ⟨M, hM⟩ := gradSq_bddAbove_of_disk_germs (by omega) hg (δ := ε ^ 2) (by positivity)
  obtain ⟨Mχ, hMχ⟩ := (isCompact_closedBall (0 : ℂ) 1).exists_bound_of_continuousOn
    (continuous_gradSq_cutPC k h0 h1).continuousOn
  have hCnn : 0 ≤ C := le_trans (norm_nonneg _) (hC 0 (by simp [disk]))
  -- measurability: crossDens is continuous on the open disk
  have hmeas : AEStronglyMeasurable (crossDens k ε f) (volume.restrict disk) := by
    have hgχc : Continuous (fun w => fderiv ℝ (fun z => ((cutP k ε z) ^ 2 : ℂ)) w) :=
      (contDiff_cutPSqC k h0 h1).continuous_fderiv
        (by simp)
    refine (ContinuousOn.mul hsm.continuousOn (ContinuousOn.add
      (ContinuousOn.mul
        (Complex.continuous_conj.comp_continuousOn (continuousOn_fderivDir_of_disk hsm 1))
        ((hgχc.clm_apply continuous_const).continuousOn))
      (ContinuousOn.mul
        (Complex.continuous_conj.comp_continuousOn (continuousOn_fderivDir_of_disk hsm I))
        ((hgχc.clm_apply continuous_const).continuousOn)))).aestronglyMeasurable measurableSet_disk
  have hconst : IntegrableOn (fun _ : ℂ => C * (max M 0 + Mχ)) disk :=
    integrableOn_const measure_ball_lt_top.ne
  refine hconst.mono' hmeas (ae_restrict_of_forall_mem measurableSet_disk fun w hw => ?_)
  set a1 := fderiv ℝ f w 1
  set aI := fderiv ℝ f w I
  -- the chain rewrite `∂(cutP)² = 2·cutP·∂cutP`
  have hg1 := fderiv_cutPSqC k h0 h1 w 1
  have hgI := fderiv_cutPSqC k h0 h1 w I
  -- crossDens = 2·cutP·u·(conj a1·∂₁cutP + conj aI·∂_IcutP)
  have hval : crossDens k ε f w = (2 * (cutP k ε w : ℂ)) * (f w
      * ((starRingEnd ℂ) a1 * fderiv ℝ (cutPC k ε) w 1
        + (starRingEnd ℂ) aI * fderiv ℝ (cutPC k ε) w I)) := by
    rw [crossDens, hg1, hgI]; ring
  -- norm bound: ‖crossDens‖ ≤ cutP·C·(gradSq u + gradSq cutPC)
  have hcpnn : (0 : ℝ) ≤ cutP k ε w := cutP_nonneg k ε w
  have hb1 : ‖(starRingEnd ℂ) a1 * fderiv ℝ (cutPC k ε) w 1
      + (starRingEnd ℂ) aI * fderiv ℝ (cutPC k ε) w I‖
      ≤ (gradSq f w + gradSq (cutPC k ε) w) / 2 := by
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul, norm_mul, Complex.norm_conj, Complex.norm_conj]
    have e1 : ‖a1‖ * ‖fderiv ℝ (cutPC k ε) w 1‖
        ≤ (‖a1‖ ^ 2 + ‖fderiv ℝ (cutPC k ε) w 1‖ ^ 2) / 2 := by
      nlinarith [sq_nonneg (‖a1‖ - ‖fderiv ℝ (cutPC k ε) w 1‖)]
    have eI : ‖aI‖ * ‖fderiv ℝ (cutPC k ε) w I‖
        ≤ (‖aI‖ ^ 2 + ‖fderiv ℝ (cutPC k ε) w I‖ ^ 2) / 2 := by
      nlinarith [sq_nonneg (‖aI‖ - ‖fderiv ℝ (cutPC k ε) w I‖)]
    have hgu : gradSq f w = ‖a1‖ ^ 2 + ‖aI‖ ^ 2 := rfl
    have hgc : gradSq (cutPC k ε) w
        = ‖fderiv ℝ (cutPC k ε) w 1‖ ^ 2 + ‖fderiv ℝ (cutPC k ε) w I‖ ^ 2 := rfl
    rw [hgu, hgc]; linarith [e1, eI]
  have h2cp : ‖(2 : ℂ) * (cutP k ε w : ℂ)‖ = 2 * cutP k ε w := by
    rw [show (2 : ℂ) * (cutP k ε w : ℂ) = ((2 * cutP k ε w : ℝ) : ℂ) by push_cast; ring,
      Complex.norm_of_nonneg (by positivity)]
  have hnormbd : ‖crossDens k ε f w‖
      ≤ cutP k ε w * C * (gradSq f w + gradSq (cutPC k ε) w) := by
    rw [hval, norm_mul, h2cp, norm_mul]
    have key : ‖f w‖ * ‖(starRingEnd ℂ) a1 * fderiv ℝ (cutPC k ε) w 1
        + (starRingEnd ℂ) aI * fderiv ℝ (cutPC k ε) w I‖
        ≤ C * ((gradSq f w + gradSq (cutPC k ε) w) / 2) :=
      mul_le_mul (hC w hw) hb1 (norm_nonneg _) hCnn
    calc 2 * cutP k ε w * (‖f w‖ * ‖(starRingEnd ℂ) a1 * fderiv ℝ (cutPC k ε) w 1
            + (starRingEnd ℂ) aI * fderiv ℝ (cutPC k ε) w I‖)
        ≤ 2 * cutP k ε w * (C * ((gradSq f w + gradSq (cutPC k ε) w) / 2)) :=
          mul_le_mul_of_nonneg_left key (by positivity)
      _ = cutP k ε w * C * (gradSq f w + gradSq (cutPC k ε) w) := by ring
  -- close: cutP·C·(gradSq u + gradSq cutPC) ≤ C·(max M 0 + Mχ)
  refine hnormbd.trans ?_
  have hcpgu : cutP k ε w * gradSq f w ≤ max M 0 := by
    by_cases hz : cutP k ε w = 0
    · rw [hz, zero_mul]; exact le_max_right M 0
    · have haway : ∀ p ∈ pF k, ε ^ 2 ≤ ‖w - p‖ := by
        intro p hp
        by_contra hlt
        exact hz (cutP_eq_zero (by omega) h0 h1
          ⟨p, (mem_pF (by omega)).mp hp, le_of_lt (not_le.mp hlt)⟩)
      calc cutP k ε w * gradSq f w ≤ 1 * gradSq f w :=
            mul_le_mul_of_nonneg_right (cutP_le_one k ε w) (gradSq_nonneg _ _)
        _ = gradSq f w := one_mul _
        _ ≤ M := hM w hw haway
        _ ≤ max M 0 := le_max_left M 0
  have hcpgc : cutP k ε w * gradSq (cutPC k ε) w ≤ Mχ := by
    have hcbmem : w ∈ Metric.closedBall (0 : ℂ) 1 :=
      Metric.ball_subset_closedBall (show w ∈ Metric.ball (0 : ℂ) 1 from hw)
    have hgcnn : (0 : ℝ) ≤ gradSq (cutPC k ε) w := by unfold gradSq; positivity
    calc cutP k ε w * gradSq (cutPC k ε) w ≤ 1 * gradSq (cutPC k ε) w :=
          mul_le_mul_of_nonneg_right (cutP_le_one k ε w) hgcnn
      _ = gradSq (cutPC k ε) w := one_mul _
      _ ≤ Mχ := le_trans (le_of_eq (Real.norm_of_nonneg hgcnn).symm) (hMχ w hcbmem)
  have t1 := mul_le_mul_of_nonneg_left hcpgu hCnn
  have t2 := mul_le_mul_of_nonneg_left hcpgc hCnn
  have hexpand : cutP k ε w * C * (gradSq f w + gradSq (cutPC k ε) w)
      = C * (cutP k ε w * gradSq f w) + C * (cutP k ε w * gradSq (cutPC k ε) w) := by ring
  rw [hexpand, mul_add]
  linarith [t1, t2]

lemma integrableOn_crossDens (hk : 2 ≤ k) (hu : IsSmooth k m u) (n : ZMod (2 * m)) {ε : ℝ}
    (h0 : 0 < ε) (h1 : ε < 1) {C : ℝ} (hC : ∀ w, ‖u n w‖ ≤ C) :
    IntegrableOn (crossDens k ε (u n)) disk := by
  apply integrableOn_crossDens_of_disk_germs hk (hu.1 n) ?_ h0 h1 (fun w _ => hC w)
  intro w hw hp
  exact exists_germ_off_puncture hu n hw hp

/-- **Integrability of the full Green integrand** `⟨∇u, ∇v⟩ + conj(Δu)·v` for `v = (cutP)²·u` —
the `hInt` hypothesis of `first_green_disk`.  Assembled from the three pieces via the pointwise
decomposition. -/
lemma integrableOn_greenIntegrand (hk : 2 ≤ k) (hu : IsSmooth k m u) (hjac : IsJacobiField k m u)
    (n : ZMod (2 * m)) {ε : ℝ} (h0 : 0 < ε) (h1 : ε < 1) {C : ℝ} (hC : ∀ w, ‖u n w‖ ≤ C) :
    IntegrableOn (fun w =>
        KsIndex.GradOrtho.gradInner (u n) (fun z => ((cutP k ε z) ^ 2 : ℂ) * u n z) w
        + (starRingEnd ℂ) (KsIndex.Surface.laplacian (u n) w) * (((cutP k ε w) ^ 2 : ℂ) * u n w))
      (Metric.ball 0 1) := by
  have hpieces : IntegrableOn (fun w => (((cutP k ε w) ^ 2 : ℂ) * (gradSq (u n) w : ℂ))
      + crossDens k ε (u n) w - (((potV k w * (cutP k ε w) ^ 2 * ‖u n w‖ ^ 2 : ℝ)) : ℂ)) disk :=
    ((integrableOn_energyTestC hk hu n h0 h1).add (integrableOn_crossDens hk hu n h0 h1 hC)).sub
      (integrableOn_potTestReal hu n h0 h1 hC).ofReal
  refine hpieces.congr_fun (fun w hw => ?_) measurableSet_disk
  have hdu : DifferentiableAt ℝ (u n) w :=
    ((hu.1 n).contDiffAt (Metric.isOpen_ball.mem_nhds hw)).differentiableAt (by simp)
  rw [gradInner_testV_expand h0 h1 n hdu, conj_lap_testV hk hjac n hw]
  simp only [crossDens]; ring

/-! ### The per-copy truncated first-Green (Caccioppoli) identity -/

/-- **Per-copy identity.**  Testing `Δu = −potV·u` against `(cutP)²·u` through `first_green_disk`:
`∫_D (cutP)²|∇u_n|²  =  ∮ conj(∂_ν u_n)·(cutP)²u_n  −  ∫_D cross  +  ∫_D potV·(cutP)²·‖u_n‖²`
(as a `ℂ` identity, the truncated energy on the left).  The boundary term is exactly the seam
trace `first_green_disk` produces. -/
lemma green_percopy (hk : 2 ≤ k) (hu : IsSmooth k m u) (hsv : SeamVal k u)
    (hjac : IsJacobiField k m u) (n : ZMod (2 * m)) {ε : ℝ} (h0 : 0 < ε) (h1 : ε < 1)
    {C : ℝ} (hC : ∀ w, ‖u n w‖ ≤ C) :
    ((∫ w in Metric.ball (0 : ℂ) 1, (cutP k ε w) ^ 2 * gradSq (u n) w : ℝ) : ℂ)
      = (∫ θ in (-π : ℝ)..π, (starRingEnd ℂ) (fderivWithin ℝ (u n) (Metric.closedBall 0 1)
            (Complex.exp ((θ : ℂ) * Complex.I)) (Complex.exp ((θ : ℂ) * Complex.I)))
            * (((cutP k ε (Complex.exp ((θ : ℂ) * Complex.I))) ^ 2 : ℂ)
              * u n (Complex.exp ((θ : ℂ) * Complex.I))))
        - (∫ w in Metric.ball (0 : ℂ) 1, crossDens k ε (u n) w)
        + ((∫ w in Metric.ball (0 : ℂ) 1, potV k w * (cutP k ε w) ^ 2 * ‖u n w‖ ^ 2 : ℝ) : ℂ) := by
  have hk1 : 1 ≤ k := by omega
  have hu2x : ∀ w ∈ Metric.ball (0 : ℂ) 1, DifferentiableAt ℝ (fun z => fderiv ℝ (u n) z 1) w :=
    fun w hw => differentiableAt_fderiv_dir
      ((hu.1 n).contDiffAt (Metric.isOpen_ball.mem_nhds hw)) 1
  have hu2y : ∀ w ∈ Metric.ball (0 : ℂ) 1,
      DifferentiableAt ℝ (fun z => fderiv ℝ (u n) z Complex.I) w :=
    fun w hw => differentiableAt_fderiv_dir
      ((hu.1 n).contDiffAt (Metric.isOpen_ball.mem_nhds hw)) Complex.I
  have hv : ∀ w ∈ Metric.ball (0 : ℂ) 1,
      DifferentiableAt ℝ (fun z => ((cutP k ε z) ^ 2 : ℂ) * u n z) w :=
    fun w hw => (differentiableAt_cutPSqC k h0 h1 w).mul
      (((hu.1 n).contDiffAt (Metric.isOpen_ball.mem_nhds hw)).differentiableAt (by simp))
  have hgreen := KsIndex.FirstGreen.first_green_disk hu2x hu2y hv
    (continuousOn_flux hk1 hu hsv n 1 h0 h1)
    (continuousOn_flux hk1 hu hsv n Complex.I h0 h1)
    (integrableOn_greenIntegrand hk hu hjac n h0 h1 hC)
  have hr1 : IntegrableOn (fun w => (cutP k ε w) ^ 2 * gradSq (u n) w) (Metric.ball (0 : ℂ) 1) :=
    integrableOn_cutPSq_gradSq hk hu n h0 h1
  have hE1 := hr1.ofReal (𝕜 := ℂ)
  have hE2 : IntegrableOn (crossDens k ε (u n)) (Metric.ball (0 : ℂ) 1) :=
    integrableOn_crossDens hk hu n h0 h1 hC
  have hr3 : IntegrableOn (fun w => potV k w * (cutP k ε w) ^ 2 * ‖u n w‖ ^ 2)
      (Metric.ball (0 : ℂ) 1) := integrableOn_potTestReal hu n h0 h1 hC
  have hE3 := hr3.ofReal (𝕜 := ℂ)
  have hdecomp : (∫ w in Metric.ball (0 : ℂ) 1,
        (KsIndex.GradOrtho.gradInner (u n) (fun z => ((cutP k ε z) ^ 2 : ℂ) * u n z) w
          + (starRingEnd ℂ) (KsIndex.Surface.laplacian (u n) w) * (((cutP k ε w) ^ 2 : ℂ) * u n w)))
      = ((∫ w in Metric.ball (0 : ℂ) 1, (cutP k ε w) ^ 2 * gradSq (u n) w : ℝ) : ℂ)
        + (∫ w in Metric.ball (0 : ℂ) 1, crossDens k ε (u n) w)
        - ((∫ w in Metric.ball (0 : ℂ) 1, potV k w * (cutP k ε w) ^ 2 * ‖u n w‖ ^ 2 : ℝ) : ℂ) := by
    have hpt : ∀ w ∈ Metric.ball (0 : ℂ) 1,
        KsIndex.GradOrtho.gradInner (u n) (fun z => ((cutP k ε z) ^ 2 : ℂ) * u n z) w
          + (starRingEnd ℂ) (KsIndex.Surface.laplacian (u n) w) * (((cutP k ε w) ^ 2 : ℂ) * u n w)
          = (((cutP k ε w) ^ 2 * gradSq (u n) w : ℝ) : ℂ) + crossDens k ε (u n) w
            - ((potV k w * (cutP k ε w) ^ 2 * ‖u n w‖ ^ 2 : ℝ) : ℂ) := by
      intro w hw
      have hdu : DifferentiableAt ℝ (u n) w :=
        ((hu.1 n).contDiffAt (Metric.isOpen_ball.mem_nhds hw)).differentiableAt (by simp)
      rw [gradInner_testV_expand h0 h1 n hdu, conj_lap_testV hk hjac n hw]
      simp only [crossDens]; push_cast; ring
    have hEsum : IntegrableOn (fun w => (((cutP k ε w) ^ 2 * gradSq (u n) w : ℝ) : ℂ)
        + crossDens k ε (u n) w) (Metric.ball (0 : ℂ) 1) := hE1.add hE2
    have hadd : (∫ w in Metric.ball (0 : ℂ) 1, ((((cutP k ε w) ^ 2 * gradSq (u n) w : ℝ) : ℂ)
          + crossDens k ε (u n) w))
        = (∫ w in Metric.ball (0 : ℂ) 1, (((cutP k ε w) ^ 2 * gradSq (u n) w : ℝ) : ℂ))
          + ∫ w in Metric.ball (0 : ℂ) 1, crossDens k ε (u n) w := integral_add hE1 hE2
    have hofe : (∫ w in Metric.ball (0 : ℂ) 1, (((cutP k ε w) ^ 2 * gradSq (u n) w : ℝ) : ℂ))
        = ((∫ w in Metric.ball (0 : ℂ) 1, (cutP k ε w) ^ 2 * gradSq (u n) w : ℝ) : ℂ) :=
      integral_ofReal
    have hofp : (∫ w in Metric.ball (0 : ℂ) 1,
        ((potV k w * (cutP k ε w) ^ 2 * ‖u n w‖ ^ 2 : ℝ) : ℂ))
        = ((∫ w in Metric.ball (0 : ℂ) 1, potV k w * (cutP k ε w) ^ 2 * ‖u n w‖ ^ 2 : ℝ) : ℂ) :=
      integral_ofReal
    calc (∫ w in Metric.ball (0 : ℂ) 1,
            (KsIndex.GradOrtho.gradInner (u n) (fun z => ((cutP k ε z) ^ 2 : ℂ) * u n z) w
              + (starRingEnd ℂ) (KsIndex.Surface.laplacian (u n) w)
                * (((cutP k ε w) ^ 2 : ℂ) * u n w)))
        = ∫ w in Metric.ball (0 : ℂ) 1, ((((cutP k ε w) ^ 2 * gradSq (u n) w : ℝ) : ℂ)
              + crossDens k ε (u n) w - ((potV k w * (cutP k ε w) ^ 2 * ‖u n w‖ ^ 2 : ℝ) : ℂ)) :=
          setIntegral_congr_fun measurableSet_ball hpt
      _ = (∫ w in Metric.ball (0 : ℂ) 1, ((((cutP k ε w) ^ 2 * gradSq (u n) w : ℝ) : ℂ)
              + crossDens k ε (u n) w))
            - ∫ w in Metric.ball (0 : ℂ) 1, ((potV k w * (cutP k ε w) ^ 2 * ‖u n w‖ ^ 2 : ℝ) : ℂ) :=
          integral_sub hEsum hE3
      _ = ((∫ w in Metric.ball (0 : ℂ) 1, (((cutP k ε w) ^ 2 * gradSq (u n) w : ℝ) : ℂ))
              + ∫ w in Metric.ball (0 : ℂ) 1, crossDens k ε (u n) w)
            - ∫ w in Metric.ball (0 : ℂ) 1,
                ((potV k w * (cutP k ε w) ^ 2 * ‖u n w‖ ^ 2 : ℝ) : ℂ) := by
          rw [hadd]
      _ = ((∫ w in Metric.ball (0 : ℂ) 1, (cutP k ε w) ^ 2 * gradSq (u n) w : ℝ) : ℂ)
            + (∫ w in Metric.ball (0 : ℂ) 1, crossDens k ε (u n) w)
            - ((∫ w in Metric.ball (0 : ℂ) 1,
                potV k w * (cutP k ε w) ^ 2 * ‖u n w‖ ^ 2 : ℝ) : ℂ) := by
          rw [hofe, hofp]
  rw [hdecomp] at hgreen
  linear_combination hgreen

/-! ### Boundary-flux cancellation across the seam arcs -/

/-- The two arc families are disjoint: no circle point lies on both `arc k 0` (`Re(wᵏ)<0`) and
`arc k 1` (`Re(wᵏ)>0`). -/
lemma arc_zero_one_disjoint {k : ℕ} {w : ℂ} (h0 : w ∈ arc k 0) (h1 : w ∈ arc k 1) : False := by
  simp only [arc, Set.mem_ofPred_eq, pow_zero, pow_one, one_mul, neg_one_mul] at h0 h1
  linarith [h0.2, h1.2]

/-- `parity` collapses a shift by `2`. -/
lemma parity_add_two {m : ℕ} (n : ZMod (2 * m)) : parity m (n + 2) = parity m n := by
  have h2 : (2 : ZMod (2 * m)) = 1 + 1 := by ring
  rw [h2, ← add_assoc, map_add, map_add, map_one, add_assoc,
    show (1 : ZMod 2) + 1 = 0 from by decide, add_zero]

/-- Every non-puncture boundary point lies on one of the two seam arcs incident to copy `n`
(the giving arc `seamArc k m n` or the receiving arc `seamArc k m (n-1)`). -/
lemma mem_seamArc_or_pred {k m : ℕ} {w : ℂ} (hw : ‖w‖ = 1) (hp : w ∉ punctures k)
    (n : ZMod (2 * m)) : w ∈ seamArc k m n ∨ w ∈ seamArc k m (n - 1) := by
  have harc := mem_arc_of_not_puncture hw hp
  have hpv := parity_succ_val m n
  have hlt2 := ZMod.val_lt (parity m n)
  rw [seamArc_pred]; unfold seamArc; rw [hpv]
  rcases (by omega : (parity m n).val = 0 ∨ (parity m n).val = 1) with h | h <;>
    rcases harc with h0 | h1 <;> rw [h]
  · exact Or.inr h0
  · exact Or.inl h1
  · exact Or.inl h0
  · exact Or.inr h1

/-- The giving arc of copy `n` is disjoint from the giving arc of copy `n+1` (they are the two
distinct arc families). -/
lemma notMem_seamArc_succ {k m : ℕ} {w : ℂ} {n : ZMod (2 * m)} (hn : w ∈ seamArc k m n)
    (hn1 : w ∈ seamArc k m (n + 1)) : False := by
  have e2 : seamArc k m (n + 1) = arc k (parity m (n + 2)).val := by
    unfold seamArc; rw [show n + 1 + 1 = n + 2 from by ring]
  rw [e2, parity_add_two] at hn1
  unfold seamArc at hn
  rw [parity_succ_val] at hn
  have hlt2 := ZMod.val_lt (parity m n)
  rcases (by omega : (parity m n).val = 0 ∨ (parity m n).val = 1) with h | h <;> rw [h] at hn hn1
  · exact arc_zero_one_disjoint hn1 (by simpa using hn)
  · exact arc_zero_one_disjoint (by simpa using hn) hn1

/-- **Pointwise boundary cancellation.**  At every angle `θ`, the sum over the `2m` copies of the
boundary-flux integrand vanishes: at a puncture the cutoff kills it, and elsewhere the copies pair
`(n, n±1)` across the shared arc, cancelling by `seam_flux_pointwise_cancel_conj`. -/
lemma sum_bInt_eq_zero (hk : 1 ≤ k) (hu : IsSmooth k m u) (hsv : SeamVal k u) [NeZero m]
    {ε : ℝ} (h0 : 0 < ε) (h1 : ε < 1) (θ : ℝ) :
    ∑ n : ZMod (2 * m), (starRingEnd ℂ) (fderivWithin ℝ (u n) (Metric.closedBall 0 1)
        (Complex.exp ((θ : ℂ) * Complex.I)) (Complex.exp ((θ : ℂ) * Complex.I)))
        * (((cutP k ε (Complex.exp ((θ : ℂ) * Complex.I))) ^ 2 : ℂ)
          * u n (Complex.exp ((θ : ℂ) * Complex.I))) = 0 := by
  classical
  have : NeZero (2 * m) := ⟨by have := NeZero.ne m; omega⟩
  have : Fact (1 < 2 * m) := ⟨by have : 1 ≤ m := Nat.one_le_iff_ne_zero.mpr (NeZero.ne m); omega⟩
  set w := Complex.exp ((θ : ℂ) * Complex.I) with hw_def
  have hnorm : ‖w‖ = 1 := Complex.norm_exp_ofReal_mul_I θ
  by_cases hpunc : w ∈ punctures k
  · have hcw : cutP k ε w = 0 :=
      cutP_eq_zero hk h0 h1 ⟨w, hpunc, by rw [sub_self, norm_zero]; positivity⟩
    simp [hcw]
  · refine Finset.sum_involution
      (fun a _ => if w ∈ seamArc k m a then a + 1 else a - 1) ?_ ?_
      (fun _ _ => Finset.mem_univ _) ?_
    · -- pairwise cancellation
      intro a _
      by_cases ha : w ∈ seamArc k m a
      · simp only [if_pos ha]
        have hval := hsv a w ha
        rw [hval]
        exact seam_flux_pointwise_cancel_conj hu hsv ha (((cutP k ε w) ^ 2 : ℂ) * u a w)
      · simp only [if_neg ha]
        have hmem : w ∈ seamArc k m (a - 1) := (mem_seamArc_or_pred hnorm hpunc a).resolve_left ha
        have hidx : (a - 1 + 1 : ZMod (2 * m)) = a := by ring
        have hlem := seam_flux_pointwise_cancel_conj hu hsv hmem
          (((cutP k ε w) ^ 2 : ℂ) * u (a - 1) w)
        rw [hidx] at hlem
        have hval := hsv (a - 1) w hmem
        rw [hidx] at hval
        rw [hval]; linear_combination hlem
    · -- `τ a ≠ a`
      intro a _ _
      have h10 : (1 : ZMod (2 * m)) ≠ 0 := one_ne_zero
      by_cases ha : w ∈ seamArc k m a
      · simp only [if_pos ha]
        exact fun h => h10 (add_left_cancel (show a + 1 = a + 0 from by rw [add_zero]; exact h))
      · simp only [if_neg ha]; exact fun h => h10 (by rwa [sub_eq_self] at h)
    · -- involution
      intro a _
      by_cases ha : w ∈ seamArc k m a
      · rw [if_pos ha, if_neg (fun h => notMem_seamArc_succ ha h)]; ring
      · rw [if_neg ha, if_pos ((mem_seamArc_or_pred hnorm hpunc a).resolve_left ha)]; ring

/-- `Lε ε ≥ 1` on `(0, e⁻¹]` — the range of the Fatou cutoff scale, making the cutoff energy
`∫|∇cutP|² ≤ 4πN²Mψ²` uniform. -/
lemma one_le_Lε {ε : ℝ} (h0 : 0 < ε) (hε : ε ≤ Real.exp (-1)) : 1 ≤ Lε ε := by
  have : Real.log ε ≤ -1 := by
    calc Real.log ε ≤ Real.log (Real.exp (-1)) := Real.log_le_log h0 hε
      _ = -1 := Real.log_exp _
  simp only [Lε]; linarith

/-- **Pointwise Peter–Paul bound** on the cutoff cross density: `‖u·(conj ∇u · ∇(cutP)²)‖ ≤
½·cutP²·|∇u|² + 2·‖u‖²·|∇cutP|²` (Young with the chain factor `∂(cutP)² = 2·cutP·∂cutP`).  The
`½` energy coefficient is what the Caccioppoli absorption needs. -/
lemma crossDens_le (k : ℕ) {ε : ℝ} (h0 : 0 < ε) (h1 : ε < 1) (f : ℂ → ℂ) (w : ℂ) :
    ‖crossDens k ε f w‖
      ≤ 1 / 2 * ((cutP k ε w) ^ 2 * gradSq f w) + 2 * (‖f w‖ ^ 2 * gradSq (cutPC k ε) w) := by
  have hcp := cutP_nonneg k ε w
  have hval : crossDens k ε f w = (2 * (cutP k ε w : ℂ))
      * (f w * ((starRingEnd ℂ) (fderiv ℝ f w 1) * fderiv ℝ (cutPC k ε) w 1
          + (starRingEnd ℂ) (fderiv ℝ f w I) * fderiv ℝ (cutPC k ε) w I)) := by
    rw [crossDens, fderiv_cutPSqC k h0 h1 w 1, fderiv_cutPSqC k h0 h1 w I]; ring
  rw [hval, norm_mul,
    show ‖(2 : ℂ) * (cutP k ε w : ℂ)‖ = 2 * cutP k ε w from by
      rw [show (2 : ℂ) * (cutP k ε w : ℂ) = ((2 * cutP k ε w : ℝ) : ℂ) by push_cast; ring,
        Complex.norm_of_nonneg (by positivity)],
    norm_mul]
  have hip : ‖(starRingEnd ℂ) (fderiv ℝ f w 1) * fderiv ℝ (cutPC k ε) w 1
        + (starRingEnd ℂ) (fderiv ℝ f w I) * fderiv ℝ (cutPC k ε) w I‖
      ≤ ‖fderiv ℝ f w 1‖ * ‖fderiv ℝ (cutPC k ε) w 1‖
        + ‖fderiv ℝ f w I‖ * ‖fderiv ℝ (cutPC k ε) w I‖ := by
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul, norm_mul, Complex.norm_conj, Complex.norm_conj]
  have hprod := mul_le_mul_of_nonneg_left hip
    (mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hcp) (norm_nonneg (f w)))
  simp only [gradSq]
  nlinarith [hprod,
    sq_nonneg (cutP k ε w * ‖fderiv ℝ f w 1‖ - 2 * ‖f w‖ * ‖fderiv ℝ (cutPC k ε) w 1‖),
    sq_nonneg (cutP k ε w * ‖fderiv ℝ f w I‖ - 2 * ‖f w‖ * ‖fderiv ℝ (cutPC k ε) w I‖),
    norm_nonneg (f w), hcp]

/-- **The summed boundary flux vanishes.**  Swapping the finite sum with the boundary θ-integral
(each summand continuous, hence interval-integrable) and applying the pointwise cancellation. -/
lemma sum_bFlux_eq_zero (hk : 1 ≤ k) (hu : IsSmooth k m u) (hsv : SeamVal k u) [NeZero m]
    {ε : ℝ} (h0 : 0 < ε) (h1 : ε < 1) :
    ∑ n : ZMod (2 * m), (∫ θ in (-π : ℝ)..π,
        (starRingEnd ℂ) (fderivWithin ℝ (u n) (Metric.closedBall 0 1)
          (Complex.exp ((θ : ℂ) * Complex.I)) (Complex.exp ((θ : ℂ) * Complex.I)))
          * (((cutP k ε (Complex.exp ((θ : ℂ) * Complex.I))) ^ 2 : ℂ)
            * u n (Complex.exp ((θ : ℂ) * Complex.I)))) = 0 := by
  have hexp : Continuous (fun θ : ℝ => Complex.exp ((θ : ℂ) * Complex.I)) :=
    Complex.continuous_exp.comp (Complex.continuous_ofReal.mul continuous_const)
  have hmaps : ∀ θ : ℝ, Complex.exp ((θ : ℂ) * Complex.I) ∈ Metric.closedBall (0 : ℂ) 1 := by
    intro θ; rw [Metric.mem_closedBall, dist_zero_right]
    exact le_of_eq (Complex.norm_exp_ofReal_mul_I θ)
  have hII : ∀ n : ZMod (2 * m), IntervalIntegrable
      (fun θ => (starRingEnd ℂ) (fderivWithin ℝ (u n) (Metric.closedBall 0 1)
          (Complex.exp ((θ : ℂ) * Complex.I)) (Complex.exp ((θ : ℂ) * Complex.I)))
          * (((cutP k ε (Complex.exp ((θ : ℂ) * Complex.I))) ^ 2 : ℂ)
            * u n (Complex.exp ((θ : ℂ) * Complex.I)))) volume (-π) π := fun n =>
    ((continuousOn_flux_diag hk hu hsv n h0 h1).comp_continuous hexp hmaps).intervalIntegrable _ _
  rw [← intervalIntegral.integral_finsetSum (fun n _ => hII n)]
  simp only [sum_bInt_eq_zero hk hu hsv h0 h1, intervalIntegral.integral_zero]

/-- **Uniform truncated-energy bound.**  Summing the per-copy Caccioppoli identity, the boundary
flux cancels (`sum_bFlux_eq_zero`); the cross term is absorbed by pointwise Young (`crossDens_le`),
leaving `∑ₙ ∫ (cutP)²|∇uₙ|² ≤ 2∑ₙ∫potV(cutP)²‖uₙ‖² + 4∑ₙ∫‖uₙ‖²|∇cutP|²`, both bounded uniformly
in `ε ∈ (0, e⁻¹]`.  Hence every per-copy truncated energy is bounded by one constant `K`. -/
lemma exists_energy_bound (hk : 2 ≤ k) {u : ZMod (2 * m) → ℂ → ℂ} (hu : IsSmooth k m u)
    (hbdd : IsBounded u) (hjac : IsJacobiField k m u) (hsv : SeamVal k u) [NeZero m] :
    ∃ K : ℝ, ∀ {ε : ℝ}, 0 < ε → ε ≤ Real.exp (-1) → ∀ n,
      ∫ w in Metric.ball (0 : ℂ) 1, (cutP k ε w) ^ 2 * gradSq (u n) w ≤ K := by
  obtain ⟨C, hC⟩ := hbdd
  have hCnn : 0 ≤ C := le_trans (norm_nonneg _) (hC 0 0)
  set Ncard := (Fintype.card (ZMod (2 * m)) : ℝ) with hNcard
  set Vol := (MeasureTheory.volume (Metric.ball (0 : ℂ) 1)).toReal with hVol
  set Dmax := 4 * π * ((pF k).card : ℝ) ^ 2 * Mψ ^ 2 with hDmax
  refine ⟨2 * (Ncard * (8 * ((k : ℝ) - 1) ^ 2 * C ^ 2 * Vol)) + 4 * (Ncard * (C ^ 2 * Dmax)), ?_⟩
  intro ε h0 hε n
  have h1 : ε < 1 := hε.trans_lt (Real.exp_lt_one_iff.mpr (by norm_num))
  -- integrability of the four densities
  have hEe : ∀ j : ZMod (2 * m), IntegrableOn (fun w => (cutP k ε w) ^ 2 * gradSq (u j) w)
      (Metric.ball (0 : ℂ) 1) := fun j => integrableOn_cutPSq_gradSq hk hu j h0 h1
  have hEp : ∀ j : ZMod (2 * m), IntegrableOn
      (fun w => potV k w * (cutP k ε w) ^ 2 * ‖u j w‖ ^ 2) (Metric.ball (0 : ℂ) 1) :=
    fun j => integrableOn_potTestReal hu j h0 h1 (fun w => hC j w)
  have hgc_int : IntegrableOn (gradSq (cutPC k ε)) (Metric.ball (0 : ℂ) 1) :=
    (integrable_gradSq_cutPC k h0 h1).integrableOn
  have hEqc : ∀ j : ZMod (2 * m), IntegrableOn (fun w => ‖u j w‖ ^ 2 * gradSq (cutPC k ε) w)
      (Metric.ball (0 : ℂ) 1) := by
    intro j
    refine (hgc_int.const_mul (C ^ 2)).mono'
      (((hu.1 j).continuousOn.norm.pow 2).mul (continuous_gradSq_cutPC k h0 h1).continuousOn
        |>.aestronglyMeasurable measurableSet_ball)
      (ae_restrict_of_forall_mem measurableSet_ball fun w _ => ?_)
    have hgcnn : (0 : ℝ) ≤ gradSq (cutPC k ε) w := by unfold gradSq; positivity
    rw [Real.norm_of_nonneg (by positivity)]
    exact mul_le_mul_of_nonneg_right (by nlinarith [hC j w, norm_nonneg (u j w)]) hgcnn
  have hEcross : ∀ j : ZMod (2 * m), IntegrableOn (crossDens k ε (u j)) (Metric.ball (0 : ℂ) 1) :=
    fun j => integrableOn_crossDens hk hu j h0 h1 (fun w => hC j w)
  -- the bound density `b j = ½ cutP²|∇u|² + 2‖u‖²|∇cutP|²` and its integral
  have hbint : ∀ j : ZMod (2 * m), (∫ w in Metric.ball (0 : ℂ) 1,
      (1 / 2 * ((cutP k ε w) ^ 2 * gradSq (u j) w) + 2 * (‖u j w‖ ^ 2 * gradSq (cutPC k ε) w)))
      = 1 / 2 * (∫ w in Metric.ball (0 : ℂ) 1, (cutP k ε w) ^ 2 * gradSq (u j) w)
        + 2 * ∫ w in Metric.ball (0 : ℂ) 1, ‖u j w‖ ^ 2 * gradSq (cutPC k ε) w := by
    intro j
    rw [integral_add ((hEe j).const_mul _) ((hEqc j).const_mul _), integral_const_mul,
      integral_const_mul]
  have hbI : ∀ j : ZMod (2 * m), IntegrableOn (fun w => 1 / 2 * ((cutP k ε w) ^ 2 * gradSq (u j) w)
      + 2 * (‖u j w‖ ^ 2 * gradSq (cutPC k ε) w)) (Metric.ball (0 : ℂ) 1) :=
    fun j => ((hEe j).const_mul (1 / 2)).add ((hEqc j).const_mul 2)
  -- summed identity (boundary flux cancels)
  have hid : (∑ j : ZMod (2 * m), ((∫ w in Metric.ball (0 : ℂ) 1,
        (cutP k ε w) ^ 2 * gradSq (u j) w : ℝ) : ℂ))
      = -(∑ j : ZMod (2 * m), ∫ w in Metric.ball (0 : ℂ) 1, crossDens k ε (u j) w)
        + ∑ j : ZMod (2 * m), ((∫ w in Metric.ball (0 : ℂ) 1,
          potV k w * (cutP k ε w) ^ 2 * ‖u j w‖ ^ 2 : ℝ) : ℂ) := by
    rw [Finset.sum_congr rfl (fun j _ => green_percopy hk hu hsv hjac j h0 h1 (fun w => hC j w)),
      Finset.sum_add_distrib, Finset.sum_sub_distrib, sum_bFlux_eq_zero (by omega) hu hsv h0 h1]
    ring
  -- real part
  have hre : (∑ j : ZMod (2 * m), ∫ w in Metric.ball (0 : ℂ) 1, (cutP k ε w) ^ 2 * gradSq (u j) w)
      = -(∑ j : ZMod (2 * m), ∫ w in Metric.ball (0 : ℂ) 1, crossDens k ε (u j) w).re
        + ∑ j : ZMod (2 * m), ∫ w in Metric.ball (0 : ℂ) 1,
            potV k w * (cutP k ε w) ^ 2 * ‖u j w‖ ^ 2 := by
    have h := hid
    rw [← Complex.ofReal_sum, ← Complex.ofReal_sum] at h
    have h2 := congrArg Complex.re h
    simpa using h2
  -- absorb the cross term
  have habsorb : (∑ j : ZMod (2 * m), ∫ w in Metric.ball (0 : ℂ) 1,
        (cutP k ε w) ^ 2 * gradSq (u j) w)
      ≤ 2 * (∑ j : ZMod (2 * m), ∫ w in Metric.ball (0 : ℂ) 1,
          potV k w * (cutP k ε w) ^ 2 * ‖u j w‖ ^ 2)
        + 4 * ∑ j : ZMod (2 * m), ∫ w in Metric.ball (0 : ℂ) 1,
          ‖u j w‖ ^ 2 * gradSq (cutPC k ε) w := by
    have hcross_bd : -(∑ j : ZMod (2 * m), ∫ w in Metric.ball (0 : ℂ) 1,
          crossDens k ε (u j) w).re
        ≤ ∑ j : ZMod (2 * m), (1 / 2 * (∫ w in Metric.ball (0 : ℂ) 1,
            (cutP k ε w) ^ 2 * gradSq (u j) w)
          + 2 * ∫ w in Metric.ball (0 : ℂ) 1, ‖u j w‖ ^ 2 * gradSq (cutPC k ε) w) := by
      calc -(∑ j, ∫ w in Metric.ball (0 : ℂ) 1, crossDens k ε (u j) w).re
          ≤ ‖∑ j : ZMod (2 * m), ∫ w in Metric.ball (0 : ℂ) 1, crossDens k ε (u j) w‖ :=
            (neg_le_abs _).trans (Complex.abs_re_le_norm _)
        _ ≤ ∑ j : ZMod (2 * m), ‖∫ w in Metric.ball (0 : ℂ) 1, crossDens k ε (u j) w‖ :=
            norm_sum_le _ _
        _ ≤ ∑ j : ZMod (2 * m), (1 / 2 * (∫ w in Metric.ball (0 : ℂ) 1,
              (cutP k ε w) ^ 2 * gradSq (u j) w)
            + 2 * ∫ w in Metric.ball (0 : ℂ) 1, ‖u j w‖ ^ 2 * gradSq (cutPC k ε) w) := by
          refine Finset.sum_le_sum (fun j _ => ?_)
          calc ‖∫ w in Metric.ball (0 : ℂ) 1, crossDens k ε (u j) w‖
              ≤ ∫ w in Metric.ball (0 : ℂ) 1, ‖crossDens k ε (u j) w‖ :=
                norm_integral_le_integral_norm _
            _ ≤ ∫ w in Metric.ball (0 : ℂ) 1,
                (1 / 2 * ((cutP k ε w) ^ 2 * gradSq (u j) w)
                  + 2 * (‖u j w‖ ^ 2 * gradSq (cutPC k ε) w)) :=
                setIntegral_mono_on (hEcross j).norm (hbI j) measurableSet_ball
                  (fun w _ => crossDens_le k h0 h1 (u j) w)
            _ = _ := hbint j
    have hsl : (∑ j : ZMod (2 * m), (1 / 2 * (∫ w in Metric.ball (0 : ℂ) 1,
          (cutP k ε w) ^ 2 * gradSq (u j) w)
        + 2 * ∫ w in Metric.ball (0 : ℂ) 1, ‖u j w‖ ^ 2 * gradSq (cutPC k ε) w))
        = 1 / 2 * (∑ j : ZMod (2 * m), ∫ w in Metric.ball (0 : ℂ) 1,
            (cutP k ε w) ^ 2 * gradSq (u j) w)
          + 2 * ∑ j : ZMod (2 * m), ∫ w in Metric.ball (0 : ℂ) 1,
            ‖u j w‖ ^ 2 * gradSq (cutPC k ε) w := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    linarith [hre, hcross_bd, hsl]
  -- per-copy bound
  have hpot_bd : ∀ j : ZMod (2 * m),
      (∫ w in Metric.ball (0 : ℂ) 1, potV k w * (cutP k ε w) ^ 2 * ‖u j w‖ ^ 2)
        ≤ 8 * ((k : ℝ) - 1) ^ 2 * C ^ 2 * Vol := by
    intro j
    calc (∫ w in Metric.ball (0 : ℂ) 1, potV k w * (cutP k ε w) ^ 2 * ‖u j w‖ ^ 2)
        ≤ ∫ _ in Metric.ball (0 : ℂ) 1, 8 * ((k : ℝ) - 1) ^ 2 * C ^ 2 :=
          setIntegral_mono_on (hEp j) (integrableOn_const measure_ball_lt_top.ne)
            measurableSet_ball (fun w hw => by
              have hpotnn : 0 ≤ potV k w := by unfold potV; positivity
              have h1' : potV k w ≤ 8 * ((k : ℝ) - 1) ^ 2 := potV_le_of_disk hw
              have h2' : (cutP k ε w) ^ 2 ≤ 1 := by nlinarith [cutP_nonneg k ε w, cutP_le_one k ε w]
              have h3' : ‖u j w‖ ^ 2 ≤ C ^ 2 := by nlinarith [hC j w, norm_nonneg (u j w)]
              have hpc : potV k w * (cutP k ε w) ^ 2 ≤ 8 * ((k : ℝ) - 1) ^ 2 :=
                le_of_le_of_eq (mul_le_mul h1' h2' (sq_nonneg _) (by positivity)) (mul_one _)
              exact mul_le_mul hpc h3' (sq_nonneg _) (by positivity))
      _ = 8 * ((k : ℝ) - 1) ^ 2 * C ^ 2 * Vol := by
          rw [setIntegral_const, smul_eq_mul, MeasureTheory.measureReal_def, ← hVol]; ring
  have hqc_bd : ∀ j : ZMod (2 * m),
      (∫ w in Metric.ball (0 : ℂ) 1, ‖u j w‖ ^ 2 * gradSq (cutPC k ε) w) ≤ C ^ 2 * Dmax := by
    intro j
    calc (∫ w in Metric.ball (0 : ℂ) 1, ‖u j w‖ ^ 2 * gradSq (cutPC k ε) w)
        ≤ ∫ w in Metric.ball (0 : ℂ) 1, C ^ 2 * gradSq (cutPC k ε) w :=
          setIntegral_mono_on (hEqc j) (hgc_int.const_mul _) measurableSet_ball (fun w _ => by
            have hgcnn : (0 : ℝ) ≤ gradSq (cutPC k ε) w := by unfold gradSq; positivity
            exact mul_le_mul_of_nonneg_right (by nlinarith [hC j w, norm_nonneg (u j w)]) hgcnn)
      _ = C ^ 2 * ∫ w in Metric.ball (0 : ℂ) 1, gradSq (cutPC k ε) w := integral_const_mul _ _
      _ ≤ C ^ 2 * Dmax := by
          refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg _)
          calc (∫ w in Metric.ball (0 : ℂ) 1, gradSq (cutPC k ε) w)
              ≤ ∫ w in disk, gradSq (cutPC k ε) w := le_refl _
            _ ≤ 4 * π * ((pF k).card : ℝ) ^ 2 * Mψ ^ 2 / Lε ε := energy_cutP_le k h0 h1
            _ ≤ Dmax := by
                rw [hDmax]
                have hL := one_le_Lε h0 hε
                have hnn : (0 : ℝ) ≤ 4 * π * ((pF k).card : ℝ) ^ 2 * Mψ ^ 2 := by positivity
                rw [div_le_iff₀ (by linarith)]; nlinarith [hnn, hL]
  -- combine
  have hSE : (∑ j : ZMod (2 * m), ∫ w in Metric.ball (0 : ℂ) 1, (cutP k ε w) ^ 2 * gradSq (u j) w)
      ≤ 2 * (Ncard * (8 * ((k : ℝ) - 1) ^ 2 * C ^ 2 * Vol)) + 4 * (Ncard * (C ^ 2 * Dmax)) := by
    have hp : (∑ j : ZMod (2 * m), ∫ w in Metric.ball (0 : ℂ) 1,
        potV k w * (cutP k ε w) ^ 2 * ‖u j w‖ ^ 2)
        ≤ Ncard * (8 * ((k : ℝ) - 1) ^ 2 * C ^ 2 * Vol) := by
      rw [hNcard, ← Finset.card_univ, ← nsmul_eq_mul]
      exact (Finset.sum_le_sum (fun j _ => hpot_bd j)).trans (by rw [Finset.sum_const])
    have hq : (∑ j : ZMod (2 * m), ∫ w in Metric.ball (0 : ℂ) 1,
        ‖u j w‖ ^ 2 * gradSq (cutPC k ε) w) ≤ Ncard * (C ^ 2 * Dmax) := by
      rw [hNcard, ← Finset.card_univ, ← nsmul_eq_mul]
      exact (Finset.sum_le_sum (fun j _ => hqc_bd j)).trans (by rw [Finset.sum_const])
    linarith [habsorb, hp, hq]
  -- extract the copy `n`
  refine le_trans ?_ hSE
  exact Finset.single_le_sum
    (f := fun j => ∫ w in Metric.ball (0 : ℂ) 1, (cutP k ε w) ^ 2 * gradSq (u j) w)
    (fun j _ => setIntegral_nonneg measurableSet_ball
      (fun w _ => mul_nonneg (sq_nonneg _) (gradSq_nonneg _ _))) (Finset.mem_univ n)

/-! ### The Caccioppoli obligation (the analytic heart — Phase 2) -/

/-- **Finite Dirichlet energy of a bounded smooth Jacobi field.**  The one genuine analytic
obligation of O1.  Fatou (`integrableOn_of_cutP_bound`) reduces it to the uniform truncated-energy
bound `exists_energy_bound` (its per-`ε` integrability is step-(0)'s `integrableOn_cutPSq_gradSq`).
The uniform bound is the summed Caccioppoli identity: per-copy first Green (`green_percopy`), the
seam boundary flux cancelling on summation (`sum_bFlux_eq_zero`), and the cutoff cross term absorbed
by Peter–Paul (`crossDens_le`). -/
lemma finiteDirichlet_of_boundedJacobi (hk : 2 ≤ k) {u : ZMod (2 * m) → ℂ → ℂ} [NeZero m]
    (hsm : IsSmooth k m u) (hbdd : IsBounded u) (hjac : IsJacobiField k m u)
    (hsv : SeamVal k u) (n : ZMod (2 * m)) :
    IntegrableOn (gradSq (u n)) disk := by
  obtain ⟨K, hKb⟩ := exists_energy_bound hk hsm hbdd hjac hsv
  exact (integrableOn_of_cutP_bound (by omega) (measurable_gradSq (u n)).aestronglyMeasurable
    (fun w _ => gradSq_nonneg _ _)
    (fun j => integrableOn_cutPSq_gradSq hk hsm n (cutoffEps_pos j) (cutoffEps_lt_one j))
    (fun j => hKb (cutoffEps_pos j) (cutoffEps_le_exp_neg_one j) n)).1

/-! ### The one-sided inclusion `BoundedJacobi ≤ EnergySmooth` -/

/-- **O1.**  Every bounded smooth Jacobi field lies in the smooth finite-energy carrier. -/
theorem bddJacobi_le_energySmooth (hk : 2 ≤ k) [NeZero m] :
    BoundedJacobi k m ≤ EnergySmooth k m := by
  intro u hu
  obtain ⟨hsm, hbdd, hjac, hpz, hsv⟩ := hu
  obtain ⟨C, hC⟩ := hbdd
  refine ⟨hsm, fun n => finiteDirichlet_of_boundedJacobi hk hsm ⟨C, hC⟩ hjac hsv n,
    fun n => integrableOn_normSq_of_bounded n (hsm.1 n).continuousOn (fun w => hC n w), hpz, hsv⟩

end KsIndex.FaithfulInjection
