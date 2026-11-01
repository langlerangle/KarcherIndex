module

public import KsIndexLean.A3CollarConvergence
public import KsIndexLean.InteriorSmoothCore
public import KsIndexLean.BoundarySmoothCore
public import KsIndexLean.SingleCcSlitClearance

@[expose] public section


/-!
# Core membership from smooth interior and boundary pieces

This module proves membership in `NatCc k b₁ b₀` and
`ReflCc k (sgn b₁) (sgn b₀)` for closed-disk restrictions of finite sums.
The inputs are smooth interior pieces supported in the disk and smooth boundary
pieces supported in the appropriate seam domains, with puncture clearance.

For Neumann boundary pieces, global smoothness supplies one-sided extensions
and even inversion parity supplies the reflected-core condition. For Dirichlet
pieces, uniform vanishing near the unit circle and exterior vanishing supply
the required boundary conditions. Support separation supplies clearance from
the opposite family's slit. The final theorem gives eventual membership of
the assembled family in both cores; it does not prove approximation convergence.
-/

open Set MeasureTheory Filter Topology Metric
open scoped ContDiff
noncomputable section
namespace KsIndex.Trace
open KsIndex.WeakH1 KsIndex.Bracket KsIndex.SingleDisk

/-! ### `closedDiskRestriction` algebra -/

lemma closedDiskRestriction_apply_add (f g : ℂ → ℂ) (z : ℂ) :
    closedDiskRestriction (fun w => f w + g w) z =
      closedDiskRestriction f z + closedDiskRestriction g z := by
  simp only [closedDiskRestriction]
  split_ifs <;> simp

lemma closedDiskRestriction_apply_sum {ι : Type*} (t : Finset ι)
    (f : ι → ℂ → ℂ) (z : ℂ) :
    closedDiskRestriction (fun w => ∑ i ∈ t, f i w) z =
      ∑ i ∈ t, closedDiskRestriction (f i) z := by
  simp only [closedDiskRestriction]
  split_ifs
  · rfl
  · simp

/-- Disk-supported functions are fixed by the closed-disk restriction. -/
lemma closedDiskRestriction_of_disk_supported {f : ℂ → ℂ}
    (hs : tsupport f ⊆ (disk : Set ℂ)) : closedDiskRestriction f = f := by
  funext z
  simp only [closedDiskRestriction]
  split_ifs with h
  · rfl
  · symm
    apply image_eq_zero_of_notMem_tsupport
    intro hm
    exact h (KsIndex.SurfaceForm.mem_disk_iff.mp (hs hm)).le

/-- Exterior-vanishing functions are fixed by the closed-disk restriction. -/
lemma closedDiskRestriction_of_exterior_vanish {f : ℂ → ℂ}
    (hext : ∀ w : ℂ, 1 ≤ ‖w‖ → f w = 0) : closedDiskRestriction f = f := by
  funext z
  simp only [closedDiskRestriction]
  split_ifs with h
  · rfl
  · exact (hext z (not_le.mp h).le).symm

/-! ### Separation of seam supports from the opposite slit -/

lemma isClosed_slitC (k : ℕ) : IsClosed (slitC k) := by
  apply IsClosed.inter
  · exact isClosed_eq continuous_norm continuous_const
  · exact isClosed_le continuous_const
      (Complex.continuous_re.comp (continuous_pow k))

/-- Closed-`slitC` points lie outside arc-0's seam domain. -/
lemma slitC_notMem_seamDomain {k : ℕ} {p : ℂ} (hp : p ∈ slitC k) :
    p ∉ (seamDomain (boundaryArc k 0) (isOpen_boundaryArc k 0) : Set ℂ) := by
  intro hmem
  have hm := (mem_seamDomain_iff (isOpen_boundaryArc k 0) p).mp hmem
  have hpn : ‖p‖ = 1 := hp.1
  have harc : (⟨p, mem_sphere_zero_iff_norm.mpr hpn⟩ : Circle₁) ∈
      boundaryArc k 0 := hm.2 _ rfl
  have hlt : (-1 : ℝ) ^ 0 * ((p ^ k).re) < 0 := harc.2
  have hge : 0 ≤ (p ^ k).re := hp.2
  simp only [pow_zero, one_mul] at hlt
  linarith

/-- Seam domains are bounded (inside the closed 2-ball). -/
lemma seamDomain_subset_closedBall {A : Set Circle₁} (hA : IsOpen A) :
    (seamDomain A hA : Set ℂ) ⊆ Metric.closedBall (0 : ℂ) 2 := by
  intro z hz
  have h := ((mem_seamDomain_iff hA z).mp hz).1
  have h2 := (mem_annulusSet.mp h).2
  rw [Metric.mem_closedBall, dist_zero_right]
  exact h2.le

/-- Seam-supported functions have compact support. -/
lemma hasCompactSupport_of_seam_support {A : Set Circle₁} (hA : IsOpen A)
    {f : ℂ → ℂ} (hs : tsupport f ⊆ (seamDomain A hA : Set ℂ)) :
    HasCompactSupport f :=
  (isCompact_closedBall (0 : ℂ) 2).of_isClosed_subset (isClosed_tsupport f)
    (hs.trans (seamDomain_subset_closedBall hA))

/-- Compact support inside arc-0's seam domain gives uniform vanishing near
the closed `slitC`, using a thickening of the compact support. -/
lemma suppAwaySlitC_of_seam0_support {k : ℕ} {f : ℂ → ℂ}
    (hc : HasCompactSupport f)
    (hs : tsupport f ⊆
      (seamDomain (boundaryArc k 0) (isOpen_boundaryArc k 0) : Set ℂ)) :
    SuppAwaySet (slitC k) f := by
  have hopen : IsOpen (slitC k)ᶜ := (isClosed_slitC k).isOpen_compl
  have hsub : tsupport f ⊆ (slitC k)ᶜ := fun z hz hslit =>
    slitC_notMem_seamDomain hslit (hs hz)
  obtain ⟨ε, hε, hth⟩ := hc.exists_cthickening_subset_open hopen hsub
  refine ⟨ε, hε, fun w ⟨p, hp, hwp⟩ => ?_⟩
  by_contra h0
  have hw : w ∈ tsupport f := subset_closure (Function.mem_support.mpr h0)
  have hpc : p ∈ cthickening ε (tsupport f) := by
    apply mem_cthickening_of_dist_le p w ε _ hw
    rw [dist_eq_norm, norm_sub_rev]
    exact hwp.le
  exact (hth hpc) hp

/-- `SuppAwaySet` descends to the closed-disk restriction. -/
lemma suppAwaySet_closedDiskRestriction {S : Set ℂ} {f : ℂ → ℂ}
    (h : SuppAwaySet S f) : SuppAwaySet S (closedDiskRestriction f) := by
  obtain ⟨ε, hε, hv⟩ := h
  refine ⟨ε, hε, fun w hw => ?_⟩
  simp only [closedDiskRestriction]
  split_ifs
  · exact hv w hw
  · rfl

/-! ### Per-piece `NatCc` membership from the exposed clauses -/

/-- A boundary piece's closed-disk restriction lies in `NatCc k b₁ b₀`, from
the stated smoothness, support, and vanishing hypotheses. -/
theorem natCc_of_piece_clauses {k : ℕ} (_hk : 1 ≤ k) (b₁ b₀ : Bool)
    {m : ℕ} (hm : m = 0 ∨ m = 1) {g : ℂ → ℂ}
    (h1 : ContDiff ℝ ∞ g)
    (h2 : tsupport g ⊆
      (seamDomain (boundaryArc k m) (isOpen_boundaryArc k m) : Set ℂ))
    (h3 : SuppAwayP1 k (closedDiskRestriction g))
    (h5 : (if m = 1 then b₁ else b₀) = false → ∃ δ : ℝ, 0 < δ ∧
      (∀ v p : ℂ, ‖p‖ = 1 → ‖v - p‖ < δ → g v = 0) ∧
      (∀ v : ℂ, 1 ≤ ‖v‖ → g v = 0)) :
    closedDiskRestriction g ∈ NatCc k b₁ b₀ := by
  have hcdr_disk : ∀ z ∈ (disk : Set ℂ), closedDiskRestriction g z = g z :=
    fun z hz => ite_eq_left (KsIndex.SurfaceForm.mem_disk_iff.mp hz).le
  have hside : ∀ p : ℂ, OneSided (closedDiskRestriction g) p := fun p =>
    ⟨g, h1.contDiffAt, Eventually.of_forall fun w hw => hcdr_disk w hw⟩
  have hcomp := hasCompactSupport_of_seam_support (isOpen_boundaryArc k m) h2
  -- the Dirichlet clause pair covers BOTH families' `SuppAwaySet` at once
  have hpair : ∀ (S : Set ℂ), (∀ p ∈ S, ‖p‖ = 1) →
      (∃ δ : ℝ, 0 < δ ∧
        (∀ v p : ℂ, ‖p‖ = 1 → ‖v - p‖ < δ → g v = 0) ∧
        (∀ v : ℂ, 1 ≤ ‖v‖ → g v = 0)) →
      SuppAwaySet S (closedDiskRestriction g) := by
    rintro S hS ⟨δ, hδ, hv, -⟩
    exact suppAwaySet_closedDiskRestriction
      ⟨δ, hδ, fun w ⟨p, hp, hwp⟩ => hv w p (hS p hp) hwp⟩
  refine (mem_NatCc).mpr
    ⟨(h1.contDiffOn).congr hcdr_disk, ?_, ?_,
     fun w hw => ite_eq_right (not_le.mpr hw), h3⟩
  · -- ArcCond on arc 1 / slitC, flag b₁
    cases hb : b₁ with
    | true => exact fun p _ => hside p
    | false =>
      rcases hm with h0 | h1'
      · -- arc-0 piece: clearance from seam-0 support
        subst h0
        exact suppAwaySet_closedDiskRestriction
          (suppAwaySlitC_of_seam0_support hcomp h2)
      · -- arc-1 piece with b₁ = false: the Dirichlet pair
        subst h1'
        exact hpair _ (fun p hp => hp.1) (h5 (by simp [hb]))
  · -- ArcCond on arc 0 / slit, flag b₀
    cases hb : b₀ with
    | true => exact fun p _ => hside p
    | false =>
      rcases hm with h0 | h1'
      · -- arc-0 piece with b₀ = false: the Dirichlet pair
        subst h0
        exact hpair _ (fun p hp => hp.1) (h5 (by simp [hb]))
      · -- arc-1 piece: clearance from seam-1 support
        subst h1'
        exact suppAwaySet_closedDiskRestriction
          (suppAwaySlit1_of_seam1_support hcomp h2)

/-! ### Per-piece `ReflCc` membership from the exposed clauses -/

/-- The Dirichlet clause pair alone puts the restriction in every twisted
core (mirror of `singleCc_of_dirichlet_clauses`, both arcs at once). -/
theorem reflCc_of_dirichlet_clauses {k : ℕ} (hk : 1 ≤ k) (s₁ s₀ : ℂ)
    {g : ℂ → ℂ} (hsm : ContDiff ℝ ∞ g) {δ : ℝ} (hδ : 0 < δ)
    (hv : ∀ v p : ℂ, ‖p‖ = 1 → ‖v - p‖ < δ → g v = 0)
    (hext : ∀ v : ℂ, 1 ≤ ‖v‖ → g v = 0) :
    closedDiskRestriction g ∈ KsIndex.TwistSwap.ReflCc k s₁ s₀ := by
  rw [closedDiskRestriction_of_exterior_vanish hext]
  have hgerm : ∀ (s : ℂ) (w : ℂ), ‖w‖ = 1 → ContDiffAt ℝ ∞ (refl s g) w := by
    intro s w hw
    have hze : g =ᶠ[𝓝 w] 0 := by
      filter_upwards [Metric.ball_mem_nhds w hδ] with z hz
      exact hv z w hw (by simpa [dist_eq_norm] using hz)
    have hw0 : w ≠ 0 := by
      intro h; subst h; simp at hw
    have ht : Tendsto σ (𝓝 w) (𝓝 w) := by
      simpa only [σ_self hw] using (continuousAt_σ hw0).tendsto
    have hr : refl s g =ᶠ[𝓝 w] 0 := by
      filter_upwards [hze, ht.eventually hze] with z hz hi
      simp [KsIndex.SingleDisk.refl, hz, hi]
    exact contDiffAt_const.congr_of_eventuallyEq hr
  exact (KsIndex.TwistSwap.mem_ReflCc).mpr
    ⟨hsm.contDiffOn,
     fun w hw => hgerm s₁ w hw.1,
     fun w hw => hgerm s₀ w hw.1,
     fun w hw => hext w hw.le,
     ⟨δ, hδ, fun w ⟨p, hp, hwp⟩ =>
       hv w p (KsIndex.JacobiFamily.punctures_norm_eq_one hk hp) hwp⟩,
     hsm.continuous.continuousOn⟩

/-- A boundary piece's closed-disk restriction lies in
`ReflCc k (sgn b₁) (sgn b₀)`, from the stated smoothness, support, and vanishing hypotheses. -/
theorem reflCc_of_piece_clauses {k : ℕ} (hk : 1 ≤ k) (b₁ b₀ : Bool)
    {m : ℕ} (hm : m = 0 ∨ m = 1) {g : ℂ → ℂ}
    (h1 : ContDiff ℝ ∞ g)
    (h2 : tsupport g ⊆
      (seamDomain (boundaryArc k m) (isOpen_boundaryArc k m) : Set ℂ))
    (h3 : SuppAwayP1 k (closedDiskRestriction g))
    (h4 : (if m = 1 then b₁ else b₀) = true → ∀ z, g (σ z) = g z)
    (h5 : (if m = 1 then b₁ else b₀) = false → ∃ δ : ℝ, 0 < δ ∧
      (∀ v p : ℂ, ‖p‖ = 1 → ‖v - p‖ < δ → g v = 0) ∧
      (∀ v : ℂ, 1 ≤ ‖v‖ → g v = 0)) :
    closedDiskRestriction g ∈ KsIndex.TwistSwap.ReflCc k (sgn b₁) (sgn b₀) := by
  rcases hm with h0 | h1'
  · subst h0
    cases hb : b₀ with
    | true =>
      -- Neumann arc-0 piece: even parity feeds the seam-0 reflected core
      have hp : ∀ z, sgn true * g (σ z) = g z := by
        intro z
        rw [sgn_true, one_mul]
        exact h4 (by simp [hb]) z
      exact (KsIndex.TwistSwap.mem_ReflCc).mpr
        (seam0_smooth_reflected_core k (sgn b₁) (sgn true) h1 h2 hp h3)
    | false =>
      obtain ⟨δ, hδ, hv, hext⟩ := h5 (by simp [hb])
      exact reflCc_of_dirichlet_clauses hk _ _ h1 hδ hv hext
  · subst h1'
    cases hb : b₁ with
    | true =>
      have hp : ∀ z, sgn true * g (σ z) = g z := by
        intro z
        rw [sgn_true, one_mul]
        exact h4 (by simp [hb]) z
      exact (KsIndex.TwistSwap.mem_ReflCc).mpr
        (seam1_smooth_reflected_core k (sgn true) (sgn b₀) h1 h2 hp h3)
    | false =>
      obtain ⟨δ, hδ, hv, hext⟩ := h5 (by simp [hb])
      exact reflCc_of_dirichlet_clauses hk _ _ h1 hδ hv hext

/-! ### The assembled family lands in both cores -/

/-- Eventually, the closed-disk restriction of the finite sum of interior
and boundary pieces lies in both the natural and reflected cores, under the
stated eventual smoothness, support, parity, and vanishing hypotheses. -/
theorem assembly_family_mem_cores {k : ℕ} (hk : 1 ≤ k) (b₁ b₀ : Bool)
    {ι : Type*} {t : Finset ι} {a : ι → ℕ} {g : ι → ℕ → ℂ → ℂ} {g₀ : ℕ → ℂ → ℂ}
    (ha : ∀ i ∈ t, a i = 0 ∨ a i = 1)
    (hC : ∀ᶠ n in atTop, ContDiff ℝ ∞ (g₀ n) ∧ tsupport (g₀ n) ⊆ (disk : Set ℂ))
    (hD : ∀ i ∈ t, ∀ᶠ n in atTop,
      ContDiff ℝ ∞ (g i n) ∧
      tsupport (g i n) ⊆
        (seamDomain (boundaryArc k (a i)) (isOpen_boundaryArc k (a i)) : Set ℂ) ∧
      SuppAwayP1 k (closedDiskRestriction (g i n)) ∧
      ((if a i = 1 then b₁ else b₀) = true → ∀ z, g i n (σ z) = g i n z) ∧
      ((if a i = 1 then b₁ else b₀) = false → ∃ δ : ℝ, 0 < δ ∧
        (∀ v p : ℂ, ‖p‖ = 1 → ‖v - p‖ < δ → g i n v = 0) ∧
        (∀ v : ℂ, 1 ≤ ‖v‖ → g i n v = 0))) :
    ∀ᶠ n in atTop,
      closedDiskRestriction (fun z => g₀ n z + ∑ i ∈ t, g i n z)
        ∈ NatCc k b₁ b₀ ∧
      closedDiskRestriction (fun z => g₀ n z + ∑ i ∈ t, g i n z)
        ∈ KsIndex.TwistSwap.ReflCc k (sgn b₁) (sgn b₀) := by
  filter_upwards [hC, (eventually_all_finset t).mpr hD] with n hCn hDn
  have hsplit : closedDiskRestriction (fun z => g₀ n z + ∑ i ∈ t, g i n z)
      = closedDiskRestriction (g₀ n)
        + ∑ i ∈ t, closedDiskRestriction (g i n) := by
    funext z
    simp only [Pi.add_apply, Finset.sum_apply, closedDiskRestriction]
    split_ifs
    · rfl
    · simp
  have h0 : closedDiskRestriction (g₀ n) = g₀ n :=
    closedDiskRestriction_of_disk_supported hCn.2
  rw [hsplit, h0]
  constructor
  · refine Submodule.add_mem _
      ((mem_NatCc).mpr (smooth_disk_supported_natural hk b₁ b₀ hCn.1 hCn.2))
      (Submodule.sum_mem _ fun i hi => ?_)
    obtain ⟨d1, d2, d3, _, d5⟩ := hDn i hi
    exact natCc_of_piece_clauses hk b₁ b₀ (ha i hi) d1 d2 d3 d5
  · refine Submodule.add_mem _
      ((KsIndex.TwistSwap.mem_ReflCc).mpr
        (smooth_disk_supported_reflected hk (sgn b₁) (sgn b₀) hCn.1 hCn.2))
      (Submodule.sum_mem _ fun i hi => ?_)
    obtain ⟨d1, d2, d3, d4, d5⟩ := hDn i hi
    exact reflCc_of_piece_clauses hk b₁ b₀ (ha i hi) d1 d2 d3 d4 d5

end KsIndex.Trace
