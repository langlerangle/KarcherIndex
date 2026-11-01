module

/-
# Boundedness of finite-gradient-energy Jacobi fields

For k >= 2 and positive period parameter m, a Jacobi field in
`GradEnergySmooth k m` is bounded. The carrier includes smoothness, seam
compatibility and normalized puncture values as well as finite gradient
energy; no per-copy value-L² assumption is added.

The proof derives value and derivative L² bounds in an end chart, applies
puncture removability to obtain a local bound, and transfers that bound to
all copies using chart coverage. Compactness bounds the part away from the
finitely many punctures. The intermediate chart bound takes its L² inputs
as hypotheses; `endField_memLp_bundle_general` supplies them below.
-/
public import KsIndexLean.GammaEndProducer
public import KsIndexLean.EndFieldWitnessGeneralK
public import KsIndexLean.EndFieldEnergyProofGeneralK
public import KsIndexLean.GradEnergySmooth

@[expose] public section


noncomputable section
open Set MeasureTheory Complex TopologicalSpace
open KsIndex.Surface KsIndex.EndChart KsIndex.B2
  KsIndex.FaithfulInjection KsIndex.PunctureRemoval KsIndex.EndField KsIndex.PunctureCutoff

namespace KsIndex.GammaProducer

/-! ### Transferring an end-chart bound to all copies

Coverage supplies the bound at nonpuncture points inside the closed disk.
The carrier's normalized puncture values and exterior zero extension handle
the remaining points. The chart bound and coverage are explicit hypotheses. -/
theorem near_puncture_bound_general {k m : ℕ} {u : ZMod (2 * m) → ℂ → ℂ}
    (hu : u ∈ GradEnergySmooth k m) {p : ℂ} (hp : p ∈ punctures k) (idx : ℂ → ZMod (2 * m))
    (hbd : ∃ δ : ℝ, 0 < δ ∧ ∃ M : ℝ, ∀ ζ : ℂ, dist ζ 0 < δ → ζ ≠ 0 →
      ‖endFieldWith p u idx ζ‖ ≤ M)
    (hcov : ∀ r : ℝ, 0 < r → ∃ δ : ℝ, 0 < δ ∧ ∀ (n : ZMod (2 * m)) (w : ℂ),
      ‖w - p‖ < δ → ‖w‖ ≤ 1 → w ≠ p →
        ∃ ζ : ℂ, 0 < ‖ζ‖ ∧ ‖ζ‖ < r ∧ endFieldWith p u idx ζ = u n w) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ C : ℝ, ∀ (n : ZMod (2 * m)) (w : ℂ), ‖w - p‖ < δ → ‖u n w‖ ≤ C := by
  obtain ⟨hsm, -, hpz, -⟩ := hu
  obtain ⟨δ', hδ', M, hM⟩ := hbd
  obtain ⟨δ, hδ, hcovδ⟩ := hcov δ' hδ'
  refine ⟨δ, hδ, max M 0, fun n w hw => ?_⟩
  by_cases hwp : w = p
  · rw [hwp, hpz n p hp]; simpa only [norm_zero] using le_max_right M 0
  · by_cases hw1 : 1 < ‖w‖
    · rw [hsm.2.2 n w hw1]; simpa only [norm_zero] using le_max_right M 0
    · obtain ⟨ζ, hζ0, hζr, heq⟩ := hcovδ n w hw (not_lt.mp hw1) hwp
      rw [← heq]
      exact le_trans (hM ζ (by rw [dist_zero_right]; exact hζr) (norm_pos_iff.mp hζ0))
        (le_max_left _ _)

/-! ### Boundedness of the chart field from finite energy

The general-k smoothness and PDE witnesses use `generalEndPotential k p m`.
The caller supplies a parity choice, positivity of the arc-sign polynomial
on the punctured chart disk, and the value and two component-gradient L²
bounds. Local removability then gives a bound near the chart origin. -/
lemma chartField_bounded_endIdx_general {k m : ℕ} [NeZero m] (hk : 2 ≤ k)
    {u : ZMod (2 * m) → ℂ → ℂ} (hu : u ∈ GradEnergySmooth k m) (hjac : IsJacobiField k m u)
    {p : ℂ} (hp : p ∈ punctures k) (c : ZMod (2 * m))
    (hbit : 0 < (-1 : ℝ) ^ (parity m c).val * (p ^ k).im) {r₀ : ℝ}
    (hr₀ : 0 < r₀) (hr₀1 : r₀ ≤ 1)
    (hSdom : ∀ z : ℂ, z ∈ Metric.ball (0 : ℂ) r₀ → z ≠ 0 →
      0 < (Sk k ((starRingEnd ℂ) p * endChart p m z)).re)
    (hu2 : MemLp (endFieldWith p u (endIdx m c p)) 2 (volume.restrict (Metric.ball 0 r₀)))
    (hgr : MemLp (gradEnc (fun z => (endFieldWith p u (endIdx m c p) z).re)) 2
      (volume.restrict (Metric.ball 0 r₀)))
    (hgi : MemLp (gradEnc (fun z => (endFieldWith p u (endIdx m c p) z).im)) 2
      (volume.restrict (Metric.ball 0 r₀))) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ M : ℝ, ∀ ζ : ℂ, dist ζ 0 < δ → ζ ≠ 0 →
      ‖endFieldWith p u (endIdx m c p) ζ‖ ≤ M := by
  have hp1 : ‖p‖ = 1 := norm_eq_one_of_mem_punctures_k (by omega) hp
  have hz₀ : (0 : ℂ) ∈ (⟨Metric.ball 0 r₀, Metric.isOpen_ball⟩ : Opens ℂ).carrier :=
    Metric.mem_ball_self hr₀
  have hdom : ∀ z ∈ (⟨Metric.ball 0 r₀, Metric.isOpen_ball⟩ : Opens ℂ).carrier \ {0},
      z ≠ 0 ∧ ‖z‖ ^ m < 1 := by
    intro z hz
    have hzne : z ≠ 0 := by simpa using hz.2
    have hznorm : ‖z‖ < r₀ := by
      have := hz.1; rw [Metric.mem_ball, dist_zero_right] at this; exact this
    exact ⟨hzne, pow_lt_one₀ (norm_nonneg z) (lt_of_lt_of_le hznorm hr₀1) (NeZero.ne m)⟩
  refine bounded_near_complex_of_smooth_punctured (Ω := ⟨Metric.ball 0 r₀, Metric.isOpen_ball⟩)
    (z₀ := 0) hz₀ (V := generalEndPotential k p m) (F := endFieldWith p u (endIdx m c p))
    ?_ ?_ ?_ ?_ ?_ hu2 hgr hgi
  · intro K _ hK
    obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn
      (contDiff_generalEndPotential hk p m).continuous.continuousOn
    exact ⟨C, fun z hz => by simpa [Real.norm_eq_abs] using hC z hz⟩
  · exact (contDiff_generalEndPotential hk p m).continuous.measurable
  · intro z hz
    exact endField_contDiffAt_punctured_general p hp1 hp hu.1 hu.2.2.2 c hbit z
      (hdom z hz).1 (hdom z hz).2 (hSdom z hz.1 (hdom z hz).1)
  · intro z hz
    exact endField_hre_general hk p hp1 hp hu.1 hjac hu.2.2.2 c hbit z
      (hdom z hz).1 (hdom z hz).2 (hSdom z hz.1 (hdom z hz).1)
  · intro z hz
    exact endField_him_general hk p hp1 hp hu.1 hjac hu.2.2.2 c hbit z
      (hdom z hz).1 (hdom z hz).2 (hSdom z hz.1 (hdom z hz).1)

/-! ### Compact-part bounds and finite assembly

Smoothness and seam compatibility give continuity away from the punctures.
Compactness and the finite copy index give a uniform bound there. Local end
bounds then complete the global estimate. -/
theorem gradEnergySmooth_bounded_away {k m : ℕ} [NeZero m]
    {u : ZMod (2 * m) → ℂ → ℂ} (hu : u ∈ GradEnergySmooth k m)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, ∀ n, ∀ w : ℂ, (∀ p ∈ punctures k, ε ≤ ‖w - p‖) → ‖u n w‖ ≤ C := by
  obtain ⟨hsm, -, -, hsv⟩ := hu
  set K : Set ℂ := {z : ℂ | ‖z‖ ≤ 1} ∩ ⋂ p ∈ punctures k, {z : ℂ | ε ≤ ‖z - p‖}
    with hKdef
  have hball : {z : ℂ | ‖z‖ ≤ 1} = Metric.closedBall (0 : ℂ) 1 := by
    ext z
    simp [Metric.mem_closedBall, dist_zero_right]
  have hKcompact : IsCompact K := by
    rw [hKdef, hball]
    apply (isCompact_closedBall (0 : ℂ) 1).inter_right
    exact isClosed_biInter fun p _ =>
      isClosed_le continuous_const ((continuous_id.sub continuous_const).norm)
  have hcont : ∀ n : ZMod (2 * m), ContinuousOn (u n) K := by
    intro n z hz
    have hz1 : ‖z‖ ≤ 1 := hz.1
    have hzp : z ∉ punctures k := by
      intro hmem
      have h' : ε ≤ ‖z - z‖ := Set.mem_iInter₂.mp hz.2 z hmem
      rw [sub_self, norm_zero] at h'
      exact absurd h' (not_le.mpr hε)
    exact (isSmooth_continuousWithinAt hsm hsv n hz1 hzp).mono
      Set.inter_subset_left
  choose C hC using fun n : ZMod (2 * m) =>
    hKcompact.exists_bound_of_continuousOn (hcont n)
  have : NeZero (2 * m) := ⟨by have := NeZero.ne m; omega⟩
  have hne : (Finset.univ : Finset (ZMod (2 * m))).Nonempty := Finset.univ_nonempty
  refine ⟨max ((Finset.univ : Finset (ZMod (2 * m))).sup' hne C) 0, ?_⟩
  intro n w hdist
  by_cases hw1 : ‖w‖ ≤ 1
  · have hwK : w ∈ K := ⟨hw1, Set.mem_iInter₂.mpr fun p hp => hdist p hp⟩
    calc ‖u n w‖ ≤ C n := hC n w hwK
      _ ≤ (Finset.univ : Finset (ZMod (2 * m))).sup' hne C :=
          Finset.le_sup' C (Finset.mem_univ n)
      _ ≤ _ := le_max_left _ _
  · rw [hsm.2.2 n w (not_le.mp hw1), norm_zero]
    exact le_max_right _ _

/-- A gradient-energy family with uniform all-copy bounds near every
puncture is bounded. Finite minima and maxima combine the end bounds with
`gradEnergySmooth_bounded_away`. -/
theorem isBounded_of_end_bounds_grad {k m : ℕ} [NeZero m] (hk : 1 ≤ k)
    {u : ZMod (2 * m) → ℂ → ℂ} (hu : u ∈ GradEnergySmooth k m)
    (hend : ∀ p ∈ punctures k, ∃ δ : ℝ, 0 < δ ∧ ∃ C : ℝ, ∀ n, ∀ w : ℂ,
      ‖w - p‖ < δ → ‖u n w‖ ≤ C) :
    IsBounded u := by
  classical
  choose! δf hδf Cf hCf using hend
  set S : Finset ℝ := insert (1 : ℝ) ((pF k).image δf) with hSdef
  have hSne : S.Nonempty := Finset.insert_nonempty _ _
  set ε : ℝ := S.min' hSne with hεdef
  have hεpos : 0 < ε := by
    have hmem := S.min'_mem hSne
    rw [← hεdef] at hmem
    rw [hSdef] at hmem
    rcases Finset.mem_insert.mp hmem with h1 | himg
    · rw [h1]; norm_num
    · obtain ⟨p, hp, hpe⟩ := Finset.mem_image.mp himg
      rw [← hpe]
      exact hδf p ((mem_pF hk).mp hp)
  have hεle : ∀ p ∈ punctures k, ε ≤ δf p := by
    intro p hp
    apply S.min'_le
    rw [hSdef]
    exact Finset.mem_insert_of_mem
      (Finset.mem_image_of_mem δf ((mem_pF hk).mpr hp))
  obtain ⟨C0, hC0⟩ := gradEnergySmooth_bounded_away hu hεpos
  set T : Finset ℝ := insert (0 : ℝ) ((pF k).image Cf) with hTdef
  have hTne : T.Nonempty := Finset.insert_nonempty _ _
  set Cend : ℝ := T.max' hTne with hCenddef
  have hCle : ∀ p ∈ punctures k, Cf p ≤ Cend := by
    intro p hp
    apply T.le_max'
    rw [hTdef]
    exact Finset.mem_insert_of_mem
      (Finset.mem_image_of_mem Cf ((mem_pF hk).mpr hp))
  refine ⟨max Cend C0, fun n w => ?_⟩
  by_cases hnear : ∃ p ∈ punctures k, ‖w - p‖ < δf p
  · obtain ⟨p, hp, hwp⟩ := hnear
    calc ‖u n w‖ ≤ Cf p := hCf p hp n w hwp
      _ ≤ Cend := hCle p hp
      _ ≤ max Cend C0 := le_max_left _ _
  · push Not at hnear
    have hfar : ∀ p ∈ punctures k, ε ≤ ‖w - p‖ := fun p hp =>
      le_trans (hεle p hp) (hnear p hp)
    calc ‖u n w‖ ≤ C0 := hC0 n w hfar
      _ ≤ max Cend C0 := le_max_right _ _

/-! ### End-chart integrability and global boundedness -/

/-- Value and component-gradient L² bounds on the full chart disk of
radius `R`, derived from the gradient-energy carrier. The larger radius
`r₀` supplies a neighborhood for the smoothness and derivative witnesses;
`hSdom` retains the required arc-sign positivity there. -/
theorem endField_memLp_bundle_general {k m : ℕ} (hk : 2 ≤ k) (hm : 0 < m)
    (u : GradEnergySmooth k m) (p : ℂ) (hp : p ∈ punctures k) (c : ZMod (2 * m))
    (hbit : 0 < (-1 : ℝ) ^ (parity m c).val * (p ^ k).im)
    {R r₀ : ℝ} (hR : 0 < R) (hRr : R < r₀) (hr₀1 : r₀ ≤ 1)
    (hSdom : ∀ z : ℂ, 0 < ‖z‖ → ‖z‖ < r₀ →
      0 < (Sk k ((starRingEnd ℂ) p * endChart p m z)).re) :
    MemLp (endFieldWith p u.val (endIdx m c p)) 2 (volume.restrict (Metric.ball (0 : ℂ) R)) ∧
    MemLp (gradEnc (fun z => (endFieldWith p u.val (endIdx m c p) z).re)) 2
      (volume.restrict (Metric.ball 0 R)) ∧
    MemLp (gradEnc (fun z => (endFieldWith p u.val (endIdx m c p) z).im)) 2
      (volume.restrict (Metric.ball 0 R)) := by
  have hp1 : ‖p‖ = 1 := norm_eq_one_of_mem_punctures_k (by omega) hp
  have hsmall : ∀ z : ℂ, ‖z‖ < r₀ → ‖z‖ ^ m < 1 := fun z hz =>
    pow_lt_one₀ (norm_nonneg z) (lt_of_lt_of_le hz hr₀1) hm.ne'
  apply memLp_complex_jet_of_branch_derivatives hm u p (r₀ := r₀) hR hRr
  · intro z hz hzr
    exact endField_contDiffAt_punctured_general p hp1 hp u.property.1 u.property.2.2.2 c hbit z
      (norm_pos_iff.mp hz) (hsmall z hzr) (hSdom z hz hzr)
  · intro z hz hi
    exact ⟨endIdx m c p z, endField_fderiv_inside_energy_general u.property.1 p hp1 c
      (norm_pos_iff.mp hz.1) (hsmall z (lt_of_le_of_lt hz.2 hRr)) hi⟩
  · intro z hz ho
    exact ⟨endIdx m c p z + 1, endField_fderiv_outside_energy_general u.property.1 p hp1 c
      (norm_pos_iff.mp hz.1) (hsmall z (lt_of_le_of_lt hz.2 hRr)) ho⟩

/-- Construct a bound near each puncture, uniform over all copies.
A parity choice and a positive arc-sign radius determine smaller chart
radii. The end-chart L² bounds, removability, and shrinking coverage then
supply the bound, including the normalized puncture values. -/
theorem end_bounds_of_jacobi_general {k m : ℕ} (hk : 2 ≤ k) [NeZero m]
    {u : ZMod (2 * m) → ℂ → ℂ} (hu : u ∈ GradEnergySmooth k m) (hjac : IsJacobiField k m u) :
    ∀ p ∈ punctures k, ∃ δ : ℝ, 0 < δ ∧ ∃ C : ℝ, ∀ n (w : ℂ),
      ‖w - p‖ < δ → ‖u n w‖ ≤ C := by
  intro p hp
  have hm : 0 < m := Nat.pos_of_ne_zero (NeZero.ne m)
  have hp1 : ‖p‖ = 1 := norm_eq_one_of_mem_punctures_k (by omega) hp
  have hsv : SeamVal k u := hu.2.2.2
  have hpz : PunctureZero k u := hu.2.2.1
  obtain ⟨c, hbit⟩ := exists_parity_pin_general (m := m) hp
  obtain ⟨rk, hrk_pos, hrk⟩ := exists_Sk_endChart_radius (show 0 < k by omega)
  set r₀ : ℝ := min 1 rk with hr₀def
  have hr₀1 : r₀ ≤ 1 := min_le_left _ _
  have hr₀rk : r₀ ≤ rk := min_le_right _ _
  set R : ℝ := r₀ / 2 with hRdef
  have hRpos : 0 < R := by rw [hRdef]; have := lt_min (one_pos) hrk_pos; positivity
  have hRr : R < r₀ := by rw [hRdef]; have := lt_min (one_pos) hrk_pos; linarith
  have hSdom : ∀ z : ℂ, 0 < ‖z‖ → ‖z‖ < r₀ →
      0 < (Sk k ((starRingEnd ℂ) p * endChart p m z)).re := by
    intro z _ hzr
    refine hrk m hp1 ?_
    have hz1 : ‖z‖ ≤ 1 := le_of_lt (lt_of_lt_of_le hzr hr₀1)
    calc ‖z‖ ^ m ≤ ‖z‖ := pow_le_of_le_one (norm_nonneg z) hz1 (NeZero.ne m)
      _ < r₀ := hzr
      _ ≤ rk := hr₀rk
  obtain ⟨hu2, hgr, hgi⟩ :=
    endField_memLp_bundle_general hk hm ⟨u, hu⟩ p hp c hbit hRpos hRr hr₀1 hSdom
  refine near_puncture_bound_general hu hp (endIdx m c p) ?_ ?_
  · exact chartField_bounded_endIdx_general hk hu hjac hp c hbit hRpos
      (le_of_lt (lt_of_lt_of_le hRr hr₀1))
      (fun z hzR hz0 => hSdom z (norm_pos_iff.mpr hz0)
        (lt_trans (by rwa [Metric.mem_ball, dist_zero_right] at hzR) hRr))
      hu2 hgr hgi
  · exact endField_coverage_general hm p hp1 hsv hpz c

/-- For k >= 2 and positive m, a Jacobi field in `GradEnergySmooth k m`
is bounded. This is the finite-Dirichlet-energy-to-boundedness direction;
no per-copy value-L² hypothesis is required. -/
theorem bounded_of_jacobi_gradEnergySmooth {k m : ℕ} (hk : 2 ≤ k) [NeZero m]
    {u : ZMod (2 * m) → ℂ → ℂ} (hu : u ∈ GradEnergySmooth k m) (hjac : IsJacobiField k m u) :
    IsBounded u :=
  isBounded_of_end_bounds_grad (by omega) hu (end_bounds_of_jacobi_general hk hu hjac)

end KsIndex.GammaProducer
