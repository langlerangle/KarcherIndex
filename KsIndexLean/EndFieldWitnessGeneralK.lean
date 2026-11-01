module

/-
# Smoothness and the Jacobi equation in general end charts

For a unit puncture `p`, the chart `endChart p m ζ = p + ζ^m` and the
sheet index `endIdx m c p` define the local field
`F = endFieldWith p u (endIdx m c p)`. Given `IsSmooth k m u`, seam-value
matching and a sheet parity satisfying
`0 < (-1)^(parity m c).val * Im(p^k)`, this file proves that `F` is `C²`
at every nonzero `ζ` satisfying `‖ζ‖^m < 1` and
`0 < Re(Sk k (conj(p) * endChart p m ζ))`.

For `k ≥ 2`, the additional hypothesis `IsJacobiField k m u` gives
`ΔF + generalEndPotential k p m * F = 0` on the same domain. The final
results give the corresponding `lapReal` equations for the real and
imaginary parts. These are punctured-chart conclusions; no extension
through `ζ = 0` is asserted here.

The positivity condition depends on `k`. Since
`‖conj(p) * endChart p m ζ - 1‖ = ‖ζ‖^m`, positivity of `Re(Sk k q)`
near `q = 1` supplies a radius `r_k > 0` for every `k > 0`.
`exists_Sk_endChart_radius` proves positivity when `‖ζ‖^m < r_k`;
the smoothness and PDE results retain it as an explicit hypothesis.

Near a seam, the field agrees with either a directly glued field or a
reflected glued field composed with the end chart. Arc membership is
propagated by continuity, while the positivity condition transfers the
sign of the angular sine to `Im(q^k)` and selects the required arc.
A continuous argument lift handles the principal argument cut. The
local representations then transfer the flat Jacobi equation through
the chart, including its transformed potential.
-/
public import KsIndexLean.EndFieldGeneralK

@[expose] public section


noncomputable section
open Complex Filter Topology
open scoped ContDiff
namespace KsIndex.EndField
open KsIndex.Surface KsIndex.EndChart KsIndex.B2 KsIndex.PunctureRemoval KsIndex.FaithfulInjection

/-! ### The radius for positivity of `Re(Sk k q)`

For unit `p`, the identity `‖conj(p) * endChart p m ζ - 1‖ = ‖ζ‖^m`
translates the neighborhood condition near `q = 1` into a chart condition. -/

/-- `‖conj(p)·endChart − 1‖ = ‖ζ‖^m` (since `q − 1 = conj(p)·ζ^m` and `‖conj p‖ = ‖p‖ = 1`). -/
lemma norm_conj_mul_endChart_sub_one {p : ℂ} (hp : ‖p‖ = 1) (m : ℕ) (ζ : ℂ) :
    ‖(starRingEnd ℂ) p * endChart p m ζ - 1‖ = ‖ζ‖ ^ m := by
  rw [conj_mul_endChart hp m ζ, add_sub_cancel_left, norm_mul, RCLike.norm_conj, hp, one_mul,
    norm_pow]

/-- **The `k`-dependent chart radius.**  There is `r_k > 0` such that for every `m`, every
`‖p‖ = 1` and every `ζ` with `‖ζ‖^m < r_k`, the `S_k`-positivity `0 < Re(S_k(conj p·endChart))`
holds — the exact condition the general-`k` arc-sign lemmas (`q_imKpow_pos/neg`) consume. -/
lemma exists_Sk_endChart_radius {k : ℕ} (hk : 0 < k) :
    ∃ r > 0, ∀ (m : ℕ) {p ζ : ℂ}, ‖p‖ = 1 → ‖ζ‖ ^ m < r →
      0 < (Sk k ((starRingEnd ℂ) p * endChart p m ζ)).re := by
  obtain ⟨r, hr, hsub⟩ := Sk_re_pos_near_one k hk
  refine ⟨r, hr, fun m p ζ hp hlt => hsub _ ?_⟩
  rw [norm_conj_mul_endChart_sub_one hp]; exact hlt

/-! ### Smoothness across the seam

These lemmas assume membership in the relevant seam arc and propagate
it by continuity. The polynomial positivity condition is used later to
establish that membership at each point. -/

/-- Local equality with the reflected glued field under the angular and seam-arc hypotheses. -/
lemma endFieldWith_reflected_eventuallyEq_general {k m : ℕ} (p : ℂ) {u : ZMod (2 * m) → ℂ → ℂ}
    (hp : ‖p‖ = 1) (hsv : SeamVal k u) (c : ZMod (2 * m)) {ζ₀ : ℂ} {N : ℤ}
    (hne : ∀ᶠ ζ in nhds ζ₀, endChart p m ζ ≠ 0)
    (hζ : ∀ᶠ ζ in nhds ζ₀, ζ ≠ 0)
    (hb : ∀ᶠ ζ in nhds ζ₀, ‖ζ‖ ^ m ≤ 2)
    (hHbd : ∀ᶠ ζ in nhds ζ₀, -(2 * Real.pi) < angT p m ζ - angA m ζ - 2 * Real.pi * (N : ℝ)
        ∧ angT p m ζ - angA m ζ - 2 * Real.pi * (N : ℝ) < 2 * Real.pi)
    (hAint : ∀ᶠ ζ in nhds ζ₀, 0 ≤ angA m ζ ∧ angA m ζ ≤ Real.pi
        ∧ 0 ≤ angA m ζ + (angT p m ζ - angA m ζ - 2 * Real.pi * (N : ℝ))
        ∧ angA m ζ + (angT p m ζ - angA m ζ - 2 * Real.pi * (N : ℝ)) ≤ Real.pi)
    (harc : ∀ᶠ ζ in nhds ζ₀, ‖endChart p m ζ‖ = 1 →
        endChart p m ζ ∈ seamArc k m (c + 2 * (N : ZMod (2 * m)) - 1)) :
    endFieldWith p u (endIdx m c p)
      =ᶠ[nhds ζ₀] fun ζ => Surface.glue u (c + 2 * (N : ZMod (2 * m)) - 1)
        (Bracket.σ (endChart p m ζ)) := by
  filter_upwards [hne, hζ, hb, hHbd, hAint, harc] with ζ hne hζ hb hHbd hAint harc
  obtain ⟨hA0, hAle, hAH0, hAHle⟩ := hAint
  rcases lt_trichotomy (angT p m ζ - angA m ζ - 2 * Real.pi * (N : ℝ)) 0 with hlt | heq | hgt
  · have hJ : angJ p m ζ = N - 1 := angJ_eq_sub_one_of_neg (le_of_lt hHbd.1) hlt
    have hout : 1 < ‖endChart p m ζ‖ := one_lt_norm_endChart hp hζ hb hAH0 hAle hlt
    exact endFieldWith_eq_reflected_outside p u c hJ hout
  · have hJ : angJ p m ζ = N := angJ_eq_of_nonneg (le_of_eq heq.symm) hHbd.2
    have hseam : ‖endChart p m ζ‖ = 1 := norm_endChart_eq_one hp hb heq
    exact endFieldWith_eq_reflected_seam p hsv c hJ (harc hseam) hseam
  · have hJ : angJ p m ζ = N := angJ_eq_of_nonneg (le_of_lt hgt) hHbd.2
    have hin : ‖endChart p m ζ‖ < 1 := norm_endChart_lt_one hp hζ hb hA0 hAHle hgt
    exact endFieldWith_eq_reflected_inside p u c hJ hne hin

/-- The reflected local representation gives `C²` regularity at a seam point. -/
lemma endField_contDiffAt_seam_general {k m : ℕ} (p : ℂ) {u : ZMod (2 * m) → ℂ → ℂ}
    (hp : ‖p‖ = 1) (hu : IsSmooth k m u) (hsv : SeamVal k u) (c : ZMod (2 * m)) {ζ₀ : ℂ} {N : ℤ}
    (hbζ₀ : ‖ζ₀‖ ^ m ≤ 2)
    (hH0 : angT p m ζ₀ - angA m ζ₀ - 2 * Real.pi * (N : ℝ) = 0)
    (hne : ∀ᶠ ζ in nhds ζ₀, endChart p m ζ ≠ 0)
    (hζ : ∀ᶠ ζ in nhds ζ₀, ζ ≠ 0)
    (hb : ∀ᶠ ζ in nhds ζ₀, ‖ζ‖ ^ m ≤ 2)
    (hHbd : ∀ᶠ ζ in nhds ζ₀, -(2 * Real.pi) < angT p m ζ - angA m ζ - 2 * Real.pi * (N : ℝ)
        ∧ angT p m ζ - angA m ζ - 2 * Real.pi * (N : ℝ) < 2 * Real.pi)
    (hAint : ∀ᶠ ζ in nhds ζ₀, 0 ≤ angA m ζ ∧ angA m ζ ≤ Real.pi
        ∧ 0 ≤ angA m ζ + (angT p m ζ - angA m ζ - 2 * Real.pi * (N : ℝ))
        ∧ angA m ζ + (angT p m ζ - angA m ζ - 2 * Real.pi * (N : ℝ)) ≤ Real.pi)
    (harc : ∀ᶠ ζ in nhds ζ₀, ‖endChart p m ζ‖ = 1 →
        endChart p m ζ ∈ seamArc k m (c + 2 * (N : ZMod (2 * m)) - 1)) :
    ContDiffAt ℝ 2 (endFieldWith p u (endIdx m c p)) ζ₀ := by
  have hseam0 : ‖endChart p m ζ₀‖ = 1 := norm_endChart_eq_one hp hbζ₀ hH0
  have hmem0 : endChart p m ζ₀ ∈ seamArc k m (c + 2 * (N : ZMod (2 * m)) - 1) :=
    harc.self_of_nhds hseam0
  have hne0 : endChart p m ζ₀ ≠ 0 := norm_pos_iff.mp (by rw [hseam0]; norm_num)
  have hσ0 : Bracket.σ (endChart p m ζ₀) = endChart p m ζ₀ := Bracket.σ_self hseam0
  have hglueσ : ContDiffAt ℝ 2 (Surface.glue u (c + 2 * (N : ZMod (2 * m)) - 1))
      (Bracket.σ (endChart p m ζ₀)) := by
    rw [hσ0]
    exact (hu.2.1 (c + 2 * (N : ZMod (2 * m)) - 1) (endChart p m ζ₀) hmem0).of_le two_le_infty
  have hfσ : ContDiffAt ℝ 2 (fun ζ => Bracket.σ (endChart p m ζ)) ζ₀ :=
    ((Bracket.contDiffAt_σ hne0).of_le two_le_infty).comp ζ₀ (contDiffAt_endChart p m ζ₀)
  have hcomp : ContDiffAt ℝ 2
      (Surface.glue u (c + 2 * (N : ZMod (2 * m)) - 1) ∘ fun ζ => Bracket.σ (endChart p m ζ)) ζ₀ :=
    hglueσ.comp ζ₀ hfσ
  exact hcomp.congr_of_eventuallyEq
    (endFieldWith_reflected_eventuallyEq_general p hp hsv c hne hζ hb hHbd hAint harc)

/-- Seam smoothness away from the principal argument cut, using continuity of arc membership. -/
lemma endField_contDiffAt_seam_offCut_general {k m : ℕ} (p : ℂ) {u : ZMod (2 * m) → ℂ → ℂ}
    (hp : ‖p‖ = 1) (hu : IsSmooth k m u) (hsv : SeamVal k u) (c : ZMod (2 * m)) {ζ₀ : ℂ} {N : ℤ}
    (hζ₀ : ζ₀ ≠ 0) (hcut : 0 < ζ₀.re ∨ ζ₀.im ≠ 0) (hb0 : ‖ζ₀‖ ^ m < 2)
    (hH0 : angT p m ζ₀ - angA m ζ₀ - 2 * Real.pi * (N : ℝ) = 0)
    (hmem0 : endChart p m ζ₀ ∈ seamArc k m (c + 2 * (N : ZMod (2 * m)) - 1)) :
    ContDiffAt ℝ 2 (endFieldWith p u (endIdx m c p)) ζ₀ := by
  have hendcont : ContinuousAt (endChart p m) ζ₀ := (contDiffAt_endChart p m ζ₀).continuousAt
  have hA : ContinuousAt (fun ζ => angA m ζ) ζ₀ :=
    Real.continuous_arccos.continuousAt.comp
      (((continuous_norm.pow m).continuousAt).neg.div_const 2)
  have hT : ContinuousAt (fun ζ => angT p m ζ) ζ₀ :=
    ((Complex.continuousAt_arg hcut).const_mul (m : ℝ)).sub continuousAt_const
  have hH : ContinuousAt
      (fun ζ => angT p m ζ - angA m ζ - 2 * Real.pi * (N : ℝ)) ζ₀ :=
    (hT.sub hA).sub continuousAt_const
  have hseam0 : ‖endChart p m ζ₀‖ = 1 := norm_endChart_eq_one hp hb0.le hH0
  have hne0 : endChart p m ζ₀ ≠ 0 := norm_pos_iff.mp (by rw [hseam0]; norm_num)
  have hAmem := angA_mem hζ₀ hb0
  have hA0 : angA m ζ₀ ∈ Set.Ioo 0 Real.pi := ⟨by linarith [Real.pi_pos, hAmem.1], hAmem.2⟩
  have fne : ∀ᶠ ζ in nhds ζ₀, endChart p m ζ ≠ 0 := hendcont.eventually_ne hne0
  have fζ : ∀ᶠ ζ in nhds ζ₀, ζ ≠ 0 := isOpen_ne.mem_nhds hζ₀
  have fb : ∀ᶠ ζ in nhds ζ₀, ‖ζ‖ ^ m ≤ 2 := by
    filter_upwards [(continuous_norm.pow m).continuousAt.eventually_lt continuousAt_const hb0]
      with ζ h using h.le
  have fHbd : ∀ᶠ ζ in nhds ζ₀, -(2 * Real.pi) < angT p m ζ - angA m ζ - 2 * Real.pi * (N : ℝ)
      ∧ angT p m ζ - angA m ζ - 2 * Real.pi * (N : ℝ) < 2 * Real.pi := by
    have hmem : Set.Ioo (-(2 * Real.pi)) (2 * Real.pi)
        ∈ nhds (angT p m ζ₀ - angA m ζ₀ - 2 * Real.pi * (N : ℝ)) := by
      rw [hH0]; exact Ioo_mem_nhds (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos])
    filter_upwards [hH.eventually hmem] with ζ h using ⟨h.1, h.2⟩
  have fAint : ∀ᶠ ζ in nhds ζ₀, 0 ≤ angA m ζ ∧ angA m ζ ≤ Real.pi
      ∧ 0 ≤ angA m ζ + (angT p m ζ - angA m ζ - 2 * Real.pi * (N : ℝ))
      ∧ angA m ζ + (angT p m ζ - angA m ζ - 2 * Real.pi * (N : ℝ)) ≤ Real.pi := by
    have hmemA : Set.Ioo 0 Real.pi ∈ nhds (angA m ζ₀) := Ioo_mem_nhds hA0.1 hA0.2
    have hmemAH : Set.Ioo 0 Real.pi
        ∈ nhds (angA m ζ₀ + (angT p m ζ₀ - angA m ζ₀ - 2 * Real.pi * (N : ℝ))) := by
      have hval : angA m ζ₀ + (angT p m ζ₀ - angA m ζ₀ - 2 * Real.pi * (N : ℝ)) = angA m ζ₀ := by
        rw [hH0]; ring
      rw [hval]; exact Ioo_mem_nhds hA0.1 hA0.2
    filter_upwards [hA.eventually hmemA, (hA.add hH).eventually hmemAH] with ζ hfa hfah
    exact ⟨hfa.1.le, hfa.2.le, hfah.1.le, hfah.2.le⟩
  have farc : ∀ᶠ ζ in nhds ζ₀, ‖endChart p m ζ‖ = 1 →
      endChart p m ζ ∈ seamArc k m (c + 2 * (N : ZMod (2 * m)) - 1) := by
    have hsign0 : (-1 : ℝ) ^ (parity m (c + 2 * (N : ZMod (2 * m)) - 1 + 1)).val
        * ((endChart p m ζ₀) ^ k).re < 0 := by
      have h := hmem0; simp only [seamArc, arc, Set.mem_ofPred_eq] at h; exact h.2
    have hgcont : ContinuousAt (fun ζ => (-1 : ℝ) ^ (parity m (c + 2 * (N : ZMod (2 * m)) - 1 + 1)).val
        * ((endChart p m ζ) ^ k).re) ζ₀ :=
      continuousAt_const.mul (Complex.continuous_re.continuousAt.comp (hendcont.pow k))
    filter_upwards [hgcont.eventually_lt continuousAt_const hsign0] with ζ hg hnorm
    simp only [seamArc, arc, Set.mem_ofPred_eq]
    exact ⟨hnorm, hg⟩
  exact endField_contDiffAt_seam_general p hp hu hsv c hb0.le hH0 fne fζ fb fHbd fAint farc

/-- A locally constant sheet index gives the direct `C²` representation at a seam point. -/
lemma endField_contDiffAt_seam_direct_general {k m : ℕ} {u : ZMod (2 * m) → ℂ → ℂ}
    (hu : IsSmooth k m u) (p : ℂ) (idx : ℂ → ZMod (2 * m)) {ζ₀ : ℂ}
    (hidx : ∀ᶠ ζ in nhds ζ₀, idx ζ = idx ζ₀)
    (harc : endChart p m ζ₀ ∈ seamArc k m (idx ζ₀)) :
    ContDiffAt ℝ 2 (endFieldWith p u idx) ζ₀ := by
  have hgC2 : ContDiffAt ℝ 2 (Surface.glue u (idx ζ₀)) (endChart p m ζ₀) :=
    (hu.2.1 (idx ζ₀) (endChart p m ζ₀) harc).of_le two_le_infty
  have hcomp : ContDiffAt ℝ 2 (fun ζ => Surface.glue u (idx ζ₀) (endChart p m ζ)) ζ₀ :=
    hgC2.comp ζ₀ (contDiffAt_endChart p m ζ₀)
  refine hcomp.congr_of_eventuallyEq ?_
  filter_upwards [hidx] with ζ hζ
  simp only [endFieldWith, hζ]

/-! ### Pointwise smoothness away from the argument cut

The sign of `Im(q^k)`, obtained from the angular sine and positivity of
`Re(Sk k q)`, combines with the sheet parity to select a seam arc. -/

/-- **Per-point off-cut `C²`, general `k`.**  Extra hypothesis `hS : 0 < Re(S_k(conj p·endChart ζ))`
(the `k`-dependent smallness, `‖ζ‖^m < r_k`) supplies the arc-sign transfer. -/
lemma endField_contDiffAt_pt_offCut_general {k m : ℕ} {u : ZMod (2 * m) → ℂ → ℂ}
    (p : ℂ) (hp : ‖p‖ = 1) (hpunc : p ∈ punctures k) (hu : IsSmooth k m u) (hsv : SeamVal k u)
    (c : ZMod (2 * m)) {ζ : ℂ}
    (hcut : 0 < ζ.re ∨ ζ.im ≠ 0) (hζ : ζ ≠ 0) (hρ1 : ‖ζ‖ ^ m < 1)
    (hbit : 0 < (-1 : ℝ) ^ (parity m c).val * (p ^ k).im)
    (hS : 0 < (Sk k ((starRingEnd ℂ) p * endChart p m ζ)).re) :
    ContDiffAt ℝ 2 (endFieldWith p u (endIdx m c p)) ζ := by
  have hρ2 : ‖ζ‖ ^ m < 2 := lt_trans hρ1 one_lt_two
  rcases lt_trichotomy (‖endChart p m ζ‖) 1 with hlt | heq | hgt
  · exact endField_contDiffAt_offSeam_offCut hu.1 p hp c hcut hρ2.le (Or.inl hlt)
  · -- SEAM: cos T = cos A
    have hcosT : Real.cos (angT p m ζ) = Real.cos (angA m ζ) := by
      have h := endChart_normSq_sub_one_cos hp hρ2.le
      have hns1 : Complex.normSq (endChart p m ζ) = 1 := by
        rw [Complex.normSq_eq_norm_sq, heq]; norm_num
      rw [hns1] at h
      have h0 : 2 * ‖ζ‖ ^ m * (Real.cos (angT p m ζ) - Real.cos (angA m ζ)) = 0 := by linarith [h]
      rcases mul_eq_zero.mp h0 with h' | h'
      · exact absurd h' (by positivity)
      · linarith [h']
    have hAmem := angA_mem hζ hρ2
    rw [Real.cos_eq_cos_iff] at hcosT
    obtain ⟨j, hj | hj⟩ := hcosT
    · -- a₂: angA = 2jπ + angT ⟹ T = A − 2jπ (N = −j), sin T > 0
      have hT2 : angT p m ζ = angA m ζ + ((-j : ℤ) : ℝ) * (2 * Real.pi) := by
        push_cast; linear_combination -hj
      have hH0 : angT p m ζ - angA m ζ - 2 * Real.pi * (((-j : ℤ)) : ℝ) = 0 := by
        rw [hT2]; ring
      have hsinT : 0 < Real.sin (angT p m ζ) := by
        rw [hT2, Real.sin_add_int_mul_two_pi]
        exact Real.sin_pos_of_pos_of_lt_pi (by linarith [hAmem.1, Real.pi_pos]) hAmem.2
      have hQ : 0 < (((starRingEnd ℂ) p * endChart p m ζ) ^ k).im :=
        q_imKpow_pos hp hζ hsinT hS
      have hmem0 : endChart p m ζ ∈ seamArc k m (c + 2 * (((-j : ℤ)) : ZMod (2 * m)) - 1) :=
        arc_mem_of_imKpow_pos hpunc hp heq hQ (by rw [parity_add_two_mul]; exact hbit)
      exact endField_contDiffAt_seam_offCut_general p hp hu hsv c hζ hcut hρ2 hH0 hmem0
    · -- a₁: angA = 2jπ − angT ⟹ T = −A + 2jπ, sin T < 0
      have hT2 : angT p m ζ = -angA m ζ + ((j : ℤ) : ℝ) * (2 * Real.pi) := by
        linear_combination hj
      have hsinT : Real.sin (angT p m ζ) < 0 := by
        rw [hT2, Real.sin_add_int_mul_two_pi, Real.sin_neg]
        have := Real.sin_pos_of_pos_of_lt_pi (show 0 < angA m ζ by linarith [hAmem.1, Real.pi_pos])
          hAmem.2
        linarith
      have hns : ∀ i : ℤ, (angT p m ζ - angA m ζ) / (2 * Real.pi) ≠ (i : ℝ) := by
        intro i hi
        have hpi : (2 * Real.pi) ≠ 0 := by positivity
        rw [div_eq_iff hpi] at hi
        have hcomb : -angA m ζ + ((j : ℤ) : ℝ) * (2 * Real.pi) - angA m ζ
            = (i : ℝ) * (2 * Real.pi) := by rw [← hT2]; exact hi
        have hApi : angA m ζ = ((j : ℝ) - (i : ℝ)) * Real.pi := by
          linear_combination (-1 / 2 : ℝ) * hcomb
        rw [hApi] at hAmem
        have hlo : (1 : ℝ) / 2 < (j : ℝ) - (i : ℝ) := by nlinarith [hAmem.1, Real.pi_pos]
        have hhi : (j : ℝ) - (i : ℝ) < 1 := by nlinarith [hAmem.2, Real.pi_pos]
        have hlo' : (0 : ℤ) < j - i := by
          have : (0 : ℝ) < ((j - i : ℤ) : ℝ) := by push_cast; linarith [hlo]
          exact_mod_cast this
        have hhi' : (j - i : ℤ) < 1 := by
          have : ((j - i : ℤ) : ℝ) < 1 := by push_cast; linarith [hhi]
          exact_mod_cast this
        omega
      have hidx : ∀ᶠ ζ' in nhds ζ, endIdx m c p ζ' = endIdx m c p ζ := by
        filter_upwards [angJ_eventuallyEq hcut hns] with ζ' h; simp only [endIdx, h]
      have hpe : parity m (endIdx m c p ζ + 1) = parity m c + 1 := by
        simp only [endIdx]; rw [map_add, map_one, parity_add_two_mul]
      have hpar : (-1 : ℝ) ^ (parity m (endIdx m c p ζ + 1)).val * (p ^ k).im < 0 := by
        rw [hpe, neg_one_pow_parity_add_one]; nlinarith [hbit]
      have hQ : (((starRingEnd ℂ) p * endChart p m ζ) ^ k).im < 0 :=
        q_imKpow_neg hp hζ hsinT hS
      exact endField_contDiffAt_seam_direct_general hu p (endIdx m c p) hidx
        (arc_mem_of_imKpow_neg hpunc hp heq hQ hpar)
  · exact endField_contDiffAt_offSeam_offCut hu.1 p hp c hcut hρ2.le (Or.inr hgt)

/-! ### Smoothness using a continuous argument lift

A local argument lift handles points on the negative real axis. Its
integer shifts leave the sheet index unchanged, allowing the direct
and reflected seam representations to apply. -/

/-- Reflected local representation expressed using an argument lift. -/
lemma endFieldWith_reflected_eventuallyEq_lift_general {k m : ℕ} (p : ℂ)
    {u : ZMod (2 * m) → ℂ → ℂ} (hp : ‖p‖ = 1) (hsv : SeamVal k u) (c : ZMod (2 * m)) {ζ₀ : ℂ}
    {N : ℤ} (θ : ℂ → ℝ)
    (hθq : ∀ᶠ ζ in nhds ζ₀, ∃ q : ℤ, θ ζ = Complex.arg ζ + 2 * Real.pi * (q : ℝ))
    (hne : ∀ᶠ ζ in nhds ζ₀, endChart p m ζ ≠ 0)
    (hζ : ∀ᶠ ζ in nhds ζ₀, ζ ≠ 0)
    (hb : ∀ᶠ ζ in nhds ζ₀, ‖ζ‖ ^ m ≤ 2)
    (hHbd : ∀ᶠ ζ in nhds ζ₀, -(2 * Real.pi) < (m : ℝ) * θ ζ - Complex.arg p - angA m ζ
        - 2 * Real.pi * (N : ℝ) ∧ (m : ℝ) * θ ζ - Complex.arg p - angA m ζ
        - 2 * Real.pi * (N : ℝ) < 2 * Real.pi)
    (hAint : ∀ᶠ ζ in nhds ζ₀, 0 ≤ angA m ζ ∧ angA m ζ ≤ Real.pi
        ∧ 0 ≤ angA m ζ + ((m : ℝ) * θ ζ - Complex.arg p - angA m ζ - 2 * Real.pi * (N : ℝ))
        ∧ angA m ζ + ((m : ℝ) * θ ζ - Complex.arg p - angA m ζ - 2 * Real.pi * (N : ℝ)) ≤ Real.pi)
    (harc : ∀ᶠ ζ in nhds ζ₀, ‖endChart p m ζ‖ = 1 →
        endChart p m ζ ∈ seamArc k m (c + 2 * (N : ZMod (2 * m)) - 1)) :
    endFieldWith p u (endIdx m c p)
      =ᶠ[nhds ζ₀] fun ζ => Surface.glue u (c + 2 * (N : ZMod (2 * m)) - 1)
        (Bracket.σ (endChart p m ζ)) := by
  filter_upwards [hθq, hne, hζ, hb, hHbd, hAint, harc] with ζ hq hne hζ hb hHbd hAint harc
  obtain ⟨q, hq⟩ := hq
  obtain ⟨hA0, hAle, hAH0, hAHle⟩ := hAint
  have hcs : Real.cos ((m : ℝ) * θ ζ - Complex.arg p) = Real.cos (angT p m ζ) := cos_lift_eq hq
  have hendIdx : endIdx m c p ζ = c + 2 *
      ((⌊((m : ℝ) * θ ζ - Complex.arg p - angA m ζ) / (2 * Real.pi)⌋ : ℤ) : ZMod (2 * m)) := by
    rw [show ((m : ℝ) * θ ζ - Complex.arg p - angA m ζ)
        = ((m : ℝ) * (Complex.arg ζ + 2 * Real.pi * (q : ℝ)) - Complex.arg p - angA m ζ)
        from by rw [hq]]
    exact (endIdx_arg_invariant c p ζ q).symm
  rcases lt_trichotomy ((m : ℝ) * θ ζ - Complex.arg p - angA m ζ - 2 * Real.pi * (N : ℝ)) 0
    with hlt | heq | hgt
  · have hfl : ⌊((m : ℝ) * θ ζ - Complex.arg p - angA m ζ) / (2 * Real.pi)⌋ = N - 1 :=
      floor_div_two_pi_eq_sub_one (le_of_lt hHbd.1) hlt
    have hv : endIdx m c p ζ = c + 2 * ((N - 1 : ℤ) : ZMod (2 * m)) := by rw [hendIdx, hfl]
    exact endFieldWith_eq_reflected_outside_val p u c hv
      (one_lt_norm_endChart_gen hp hζ hb hcs hAH0 hAle hlt)
  · have hfl : ⌊((m : ℝ) * θ ζ - Complex.arg p - angA m ζ) / (2 * Real.pi)⌋ = N :=
      floor_div_two_pi_eq (le_of_eq heq.symm) hHbd.2
    have hv : endIdx m c p ζ = c + 2 * (N : ZMod (2 * m)) := by rw [hendIdx, hfl]
    have hseam : ‖endChart p m ζ‖ = 1 := norm_endChart_eq_one_gen hp hb hcs heq
    exact endFieldWith_eq_reflected_seam_val p hsv c hv (harc hseam) hseam
  · have hfl : ⌊((m : ℝ) * θ ζ - Complex.arg p - angA m ζ) / (2 * Real.pi)⌋ = N :=
      floor_div_two_pi_eq (le_of_lt hgt) hHbd.2
    have hv : endIdx m c p ζ = c + 2 * (N : ZMod (2 * m)) := by rw [hendIdx, hfl]
    exact endFieldWith_eq_reflected_inside_val p u c hv hne
      (norm_endChart_lt_one_gen hp hζ hb hcs hA0 hAHle hgt)

/-- Seam smoothness from a continuous argument lift and seam-arc membership. -/
lemma endField_contDiffAt_seam_lift_general {k m : ℕ} (p : ℂ) {u : ZMod (2 * m) → ℂ → ℂ}
    (hp : ‖p‖ = 1) (hu : IsSmooth k m u) (hsv : SeamVal k u) (c : ZMod (2 * m)) {ζ₀ : ℂ} {N : ℤ}
    (θ : ℂ → ℝ) (hθc : ContinuousAt θ ζ₀)
    (hθq : ∀ᶠ ζ in nhds ζ₀, ∃ q : ℤ, θ ζ = Complex.arg ζ + 2 * Real.pi * (q : ℝ))
    (hζ₀ : ζ₀ ≠ 0) (hb0 : ‖ζ₀‖ ^ m < 2)
    (hH0 : (m : ℝ) * θ ζ₀ - Complex.arg p - angA m ζ₀ - 2 * Real.pi * (N : ℝ) = 0)
    (hmem0 : endChart p m ζ₀ ∈ seamArc k m (c + 2 * (N : ZMod (2 * m)) - 1)) :
    ContDiffAt ℝ 2 (endFieldWith p u (endIdx m c p)) ζ₀ := by
  obtain ⟨q0, hq0⟩ := hθq.self_of_nhds
  have hcs0 : Real.cos ((m : ℝ) * θ ζ₀ - Complex.arg p) = Real.cos (angT p m ζ₀) := cos_lift_eq hq0
  have hseam0 : ‖endChart p m ζ₀‖ = 1 := norm_endChart_eq_one_gen hp hb0.le hcs0 hH0
  have hne0 : endChart p m ζ₀ ≠ 0 := norm_pos_iff.mp (by rw [hseam0]; norm_num)
  have hendcont : ContinuousAt (endChart p m) ζ₀ := (contDiffAt_endChart p m ζ₀).continuousAt
  have hA : ContinuousAt (fun ζ => angA m ζ) ζ₀ :=
    Real.continuous_arccos.continuousAt.comp
      (((continuous_norm.pow m).continuousAt).neg.div_const 2)
  have hH : ContinuousAt
      (fun ζ => (m : ℝ) * θ ζ - Complex.arg p - angA m ζ - 2 * Real.pi * (N : ℝ)) ζ₀ :=
    (((hθc.const_mul (m : ℝ)).sub continuousAt_const).sub hA).sub continuousAt_const
  have hAmem := angA_mem hζ₀ hb0
  have hA0 : angA m ζ₀ ∈ Set.Ioo 0 Real.pi := ⟨by linarith [Real.pi_pos, hAmem.1], hAmem.2⟩
  have fne : ∀ᶠ ζ in nhds ζ₀, endChart p m ζ ≠ 0 := hendcont.eventually_ne hne0
  have fζ : ∀ᶠ ζ in nhds ζ₀, ζ ≠ 0 := isOpen_ne.mem_nhds hζ₀
  have hb : ∀ᶠ ζ in nhds ζ₀, ‖ζ‖ ^ m ≤ 2 := by
    filter_upwards [(continuous_norm.pow m).continuousAt.eventually_lt continuousAt_const hb0]
      with ζ h using h.le
  have fHbd : ∀ᶠ ζ in nhds ζ₀, -(2 * Real.pi) < (m : ℝ) * θ ζ - Complex.arg p - angA m ζ
      - 2 * Real.pi * (N : ℝ) ∧ (m : ℝ) * θ ζ - Complex.arg p - angA m ζ
      - 2 * Real.pi * (N : ℝ) < 2 * Real.pi := by
    have hmem : Set.Ioo (-(2 * Real.pi)) (2 * Real.pi)
        ∈ nhds ((m : ℝ) * θ ζ₀ - Complex.arg p - angA m ζ₀ - 2 * Real.pi * (N : ℝ)) := by
      rw [hH0]; exact Ioo_mem_nhds (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos])
    filter_upwards [hH.eventually hmem] with ζ h using ⟨h.1, h.2⟩
  have fAint : ∀ᶠ ζ in nhds ζ₀, 0 ≤ angA m ζ ∧ angA m ζ ≤ Real.pi
      ∧ 0 ≤ angA m ζ + ((m : ℝ) * θ ζ - Complex.arg p - angA m ζ - 2 * Real.pi * (N : ℝ))
      ∧ angA m ζ + ((m : ℝ) * θ ζ - Complex.arg p - angA m ζ - 2 * Real.pi * (N : ℝ)) ≤ Real.pi := by
    have hmemA : Set.Ioo 0 Real.pi ∈ nhds (angA m ζ₀) := Ioo_mem_nhds hA0.1 hA0.2
    have hmemAH : Set.Ioo 0 Real.pi ∈ nhds (angA m ζ₀ + ((m : ℝ) * θ ζ₀ - Complex.arg p
        - angA m ζ₀ - 2 * Real.pi * (N : ℝ))) := by
      have hval : angA m ζ₀ + ((m : ℝ) * θ ζ₀ - Complex.arg p - angA m ζ₀ - 2 * Real.pi * (N : ℝ))
          = angA m ζ₀ := by rw [hH0]; ring
      rw [hval]; exact Ioo_mem_nhds hA0.1 hA0.2
    filter_upwards [hA.eventually hmemA, (hA.add hH).eventually hmemAH] with ζ hfa hfah
    exact ⟨hfa.1.le, hfa.2.le, hfah.1.le, hfah.2.le⟩
  have farc : ∀ᶠ ζ in nhds ζ₀, ‖endChart p m ζ‖ = 1 →
      endChart p m ζ ∈ seamArc k m (c + 2 * (N : ZMod (2 * m)) - 1) := by
    have hsign0 : (-1 : ℝ) ^ (parity m (c + 2 * (N : ZMod (2 * m)) - 1 + 1)).val
        * ((endChart p m ζ₀) ^ k).re < 0 := by
      have h := hmem0; simp only [seamArc, arc, Set.mem_ofPred_eq] at h; exact h.2
    have hgcont : ContinuousAt (fun ζ => (-1 : ℝ) ^ (parity m (c + 2 * (N : ZMod (2 * m)) - 1 + 1)).val
        * ((endChart p m ζ) ^ k).re) ζ₀ :=
      continuousAt_const.mul (Complex.continuous_re.continuousAt.comp (hendcont.pow k))
    filter_upwards [hgcont.eventually_lt continuousAt_const hsign0] with ζ hg hnorm
    simp only [seamArc, arc, Set.mem_ofPred_eq]
    exact ⟨hnorm, hg⟩
  have hmatch :=
    endFieldWith_reflected_eventuallyEq_lift_general p hp hsv c θ hθq fne fζ hb fHbd fAint farc
  have hσ0 : Bracket.σ (endChart p m ζ₀) = endChart p m ζ₀ := Bracket.σ_self hseam0
  have hglueσ : ContDiffAt ℝ 2 (Surface.glue u (c + 2 * (N : ZMod (2 * m)) - 1))
      (Bracket.σ (endChart p m ζ₀)) := by
    rw [hσ0]
    exact (hu.2.1 (c + 2 * (N : ZMod (2 * m)) - 1) (endChart p m ζ₀) hmem0).of_le two_le_infty
  have hfσ : ContDiffAt ℝ 2 (fun ζ => Bracket.σ (endChart p m ζ)) ζ₀ :=
    ((Bracket.contDiffAt_σ hne0).of_le two_le_infty).comp ζ₀ (contDiffAt_endChart p m ζ₀)
  have hcomp : ContDiffAt ℝ 2
      (Surface.glue u (c + 2 * (N : ZMod (2 * m)) - 1) ∘ fun ζ => Bracket.σ (endChart p m ζ)) ζ₀ :=
    hglueσ.comp ζ₀ hfσ
  exact hcomp.congr_of_eventuallyEq hmatch

/-- **Per-point `C²` on the principal cut, general `k`.**  Extra hypothesis
`hS : 0 < Re(S_k(conj p·endChart ζ₀))` supplies the arc-sign transfer (the cut `cos`/`sin` of
`angT` are pointwise, so the lift carries them through). -/
lemma endField_contDiffAt_pt_cut_general {k m : ℕ} {u : ZMod (2 * m) → ℂ → ℂ}
    (p : ℂ) (hp : ‖p‖ = 1) (hpunc : p ∈ punctures k) (hu : IsSmooth k m u) (hsv : SeamVal k u)
    (c : ZMod (2 * m)) {ζ₀ : ℂ} (hcre : ζ₀.re < 0) (hρ1 : ‖ζ₀‖ ^ m < 1)
    (hbit : 0 < (-1 : ℝ) ^ (parity m c).val * (p ^ k).im)
    (hS : 0 < (Sk k ((starRingEnd ℂ) p * endChart p m ζ₀)).re) :
    ContDiffAt ℝ 2 (endFieldWith p u (endIdx m c p)) ζ₀ := by
  have hζ₀ : ζ₀ ≠ 0 := fun h => by simp [h] at hcre
  have hρ2 : ‖ζ₀‖ ^ m < 2 := lt_trans hρ1 one_lt_two
  set θ : ℂ → ℝ := fun ζ => Complex.arg (-ζ) + Real.pi with hθdef
  have hθc : ContinuousAt θ ζ₀ := argLift_continuousAt (Or.inl hcre)
  have hθq : ∀ᶠ ζ in nhds ζ₀, ∃ q : ℤ, θ ζ = Complex.arg ζ + 2 * Real.pi * (q : ℝ) := by
    filter_upwards [isOpen_ne.mem_nhds hζ₀] with ζ hζ using argLift_arg_eq hζ
  obtain ⟨q0, hq0⟩ := hθq.self_of_nhds
  have hcs0 : Real.cos ((m : ℝ) * θ ζ₀ - Complex.arg p) = Real.cos (angT p m ζ₀) := cos_lift_eq hq0
  have hsn0 : Real.sin ((m : ℝ) * θ ζ₀ - Complex.arg p) = Real.sin (angT p m ζ₀) := sin_lift_eq hq0
  rcases lt_trichotomy (‖endChart p m ζ₀‖) 1 with hlt | heq | hgt
  · have hns : ∀ i : ℤ, ((m : ℝ) * θ ζ₀ - Complex.arg p - angA m ζ₀) / (2 * Real.pi) ≠ (i : ℝ) := by
      intro i hi
      rw [div_eq_iff (by positivity)] at hi
      have hH0k : (m : ℝ) * θ ζ₀ - Complex.arg p - angA m ζ₀ - 2 * Real.pi * (i : ℝ) = 0 := by
        linear_combination hi
      rw [norm_endChart_eq_one_gen hp hρ2.le hcs0 hH0k] at hlt; exact lt_irrefl 1 hlt
    exact endField_contDiffAt_offSeam hu.1 p (endIdx m c p)
      (endIdx_eventuallyEq_of_lift θ hθc hθq hns) (Or.inl hlt)
  · have hcosT : Real.cos (angT p m ζ₀) = Real.cos (angA m ζ₀) := by
      have h := endChart_normSq_sub_one_cos hp hρ2.le
      have hns1 : Complex.normSq (endChart p m ζ₀) = 1 := by
        rw [Complex.normSq_eq_norm_sq, heq]; norm_num
      rw [hns1] at h
      have h0 : 2 * ‖ζ₀‖ ^ m * (Real.cos (angT p m ζ₀) - Real.cos (angA m ζ₀)) = 0 := by linarith [h]
      rcases mul_eq_zero.mp h0 with h' | h'
      · exact absurd h' (by positivity)
      · linarith [h']
    have hAmem := angA_mem hζ₀ hρ2
    have hcosS : Real.cos ((m : ℝ) * θ ζ₀ - Complex.arg p) = Real.cos (angA m ζ₀) := by
      rw [hcs0, hcosT]
    rw [Real.cos_eq_cos_iff] at hcosS
    obtain ⟨j, hj | hj⟩ := hcosS
    · have hH0 : (m : ℝ) * θ ζ₀ - Complex.arg p - angA m ζ₀ - 2 * Real.pi * (((-j : ℤ)) : ℝ) = 0 := by
        push_cast; linear_combination -hj
      have hsinT : 0 < Real.sin (angT p m ζ₀) := by
        rw [← hsn0, show (m : ℝ) * θ ζ₀ - Complex.arg p
            = angA m ζ₀ + ((-j : ℤ) : ℝ) * (2 * Real.pi) from by push_cast; linear_combination -hj,
          Real.sin_add_int_mul_two_pi]
        exact Real.sin_pos_of_pos_of_lt_pi (by linarith [hAmem.1, Real.pi_pos]) hAmem.2
      have hQ : 0 < (((starRingEnd ℂ) p * endChart p m ζ₀) ^ k).im := q_imKpow_pos hp hζ₀ hsinT hS
      have hmem0 : endChart p m ζ₀ ∈ seamArc k m (c + 2 * (((-j : ℤ)) : ZMod (2 * m)) - 1) :=
        arc_mem_of_imKpow_pos hpunc hp heq hQ (by rw [parity_add_two_mul]; exact hbit)
      exact endField_contDiffAt_seam_lift_general p hp hu hsv c θ hθc hθq hζ₀ hρ2 hH0 hmem0
    · have hsS : (m : ℝ) * θ ζ₀ - Complex.arg p = -angA m ζ₀ + ((j : ℤ) : ℝ) * (2 * Real.pi) := by
        linear_combination hj
      have hsinT : Real.sin (angT p m ζ₀) < 0 := by
        rw [← hsn0, hsS, Real.sin_add_int_mul_two_pi, Real.sin_neg]
        have := Real.sin_pos_of_pos_of_lt_pi (show 0 < angA m ζ₀ by linarith [hAmem.1, Real.pi_pos])
          hAmem.2
        linarith
      have hns : ∀ i : ℤ, ((m : ℝ) * θ ζ₀ - Complex.arg p - angA m ζ₀) / (2 * Real.pi) ≠ (i : ℝ) := by
        intro i hi
        rw [div_eq_iff (by positivity)] at hi
        rw [hsS] at hi
        have hApi : angA m ζ₀ = ((j : ℝ) - (i : ℝ)) * Real.pi := by linear_combination (-1 / 2 : ℝ) * hi
        rw [hApi] at hAmem
        have hlo : (1 : ℝ) / 2 < (j : ℝ) - (i : ℝ) := by nlinarith [hAmem.1, Real.pi_pos]
        have hhi : (j : ℝ) - (i : ℝ) < 1 := by nlinarith [hAmem.2, Real.pi_pos]
        have hlo' : (0 : ℤ) < j - i := by
          have hh : (0 : ℝ) < ((j - i : ℤ) : ℝ) := by push_cast; linarith [hlo]
          exact_mod_cast hh
        have hhi' : (j - i : ℤ) < 1 := by
          have hh : ((j - i : ℤ) : ℝ) < 1 := by push_cast; linarith [hhi]
          exact_mod_cast hh
        omega
      have hpe : parity m (endIdx m c p ζ₀ + 1) = parity m c + 1 := by
        simp only [endIdx]; rw [map_add, map_one, parity_add_two_mul]
      have hpar : (-1 : ℝ) ^ (parity m (endIdx m c p ζ₀ + 1)).val * (p ^ k).im < 0 := by
        rw [hpe, neg_one_pow_parity_add_one]; nlinarith [hbit]
      have hQ : (((starRingEnd ℂ) p * endChart p m ζ₀) ^ k).im < 0 := q_imKpow_neg hp hζ₀ hsinT hS
      exact endField_contDiffAt_seam_direct_general hu p (endIdx m c p)
        (endIdx_eventuallyEq_of_lift θ hθc hθq hns)
        (arc_mem_of_imKpow_neg hpunc hp heq hQ hpar)
  · have hns : ∀ i : ℤ, ((m : ℝ) * θ ζ₀ - Complex.arg p - angA m ζ₀) / (2 * Real.pi) ≠ (i : ℝ) := by
      intro i hi
      rw [div_eq_iff (by positivity)] at hi
      have hH0k : (m : ℝ) * θ ζ₀ - Complex.arg p - angA m ζ₀ - 2 * Real.pi * (i : ℝ) = 0 := by
        linear_combination hi
      rw [norm_endChart_eq_one_gen hp hρ2.le hcs0 hH0k] at hgt; exact lt_irrefl 1 hgt
    exact endField_contDiffAt_offSeam hu.1 p (endIdx m c p)
      (endIdx_eventuallyEq_of_lift θ hθc hθq hns) (Or.inr hgt)

/-- The end field is `C²` at every nonzero `ζ` with `‖ζ‖^m < 1`
on which the `S_k`-positivity `hS` holds (the `k`-dependent smallness `‖ζ‖^m < r_k`). -/
theorem endField_contDiffAt_punctured_general {k m : ℕ} {u : ZMod (2 * m) → ℂ → ℂ} (p : ℂ)
    (hp : ‖p‖ = 1) (hpunc : p ∈ punctures k) (hu : IsSmooth k m u) (hsv : SeamVal k u)
    (c : ZMod (2 * m)) (hbit : 0 < (-1 : ℝ) ^ (parity m c).val * (p ^ k).im) :
    ∀ ζ : ℂ, ζ ≠ 0 → ‖ζ‖ ^ m < 1 → 0 < (Sk k ((starRingEnd ℂ) p * endChart p m ζ)).re →
      ContDiffAt ℝ 2 (endFieldWith p u (endIdx m c p)) ζ := by
  intro ζ hζ hρ1 hS
  by_cases hcut : 0 < ζ.re ∨ ζ.im ≠ 0
  · exact endField_contDiffAt_pt_offCut_general p hp hpunc hu hsv c hcut hζ hρ1 hbit hS
  · rw [not_or, not_lt, not_ne_iff] at hcut
    have hcre : ζ.re < 0 := lt_of_le_of_ne hcut.1
      (fun h => hζ (Complex.ext (by rw [Complex.zero_re]; exact h)
        (by rw [Complex.zero_im]; exact hcut.2)))
    exact endField_contDiffAt_pt_cut_general p hp hpunc hu hsv c hcre hρ1 hbit hS

/-! ### Local representations and the Jacobi equation

The direct and reflected representations supply a `C²` function `H`
satisfying `ΔH + potV k * H = 0` at the chart image. Composition with
the end chart yields the equation with `generalEndPotential k`. -/

/-- The reflected glued field is `C²` at the indicated seam point. -/
lemma reflectedGerm_contDiffAt_general {k m : ℕ} {u : ZMod (2 * m) → ℂ → ℂ} (hu : IsSmooth k m u)
    (j : ZMod (2 * m)) {w₀ : ℂ} (hmem : w₀ ∈ seamArc k m j) (heq : ‖w₀‖ = 1) :
    ContDiffAt ℝ 2 (Surface.glue u j ∘ Bracket.σ) w₀ := by
  have hw0 : w₀ ≠ 0 := norm_pos_iff.mp (by rw [heq]; norm_num)
  have hg : ContDiffAt ℝ 2 (Surface.glue u j) (Bracket.σ w₀) := by
    rw [Bracket.σ_self heq]; exact (hu.2.1 j w₀ hmem).of_le two_le_infty
  exact hg.comp w₀ ((Bracket.contDiffAt_σ hw0).of_le two_le_infty)

/-- The reflected glued field satisfies the flat Jacobi equation at the seam point. -/
lemma reflectedGerm_flat_general {k m : ℕ} (hk : 2 ≤ k) {u : ZMod (2 * m) → ℂ → ℂ}
    (hu : IsSmooth k m u) (hjac : IsJacobiField k m u) (j : ZMod (2 * m)) {w₀ : ℂ}
    (hmem : w₀ ∈ seamArc k m j) (heq : ‖w₀‖ = 1) :
    laplacian (Surface.glue u j ∘ Bracket.σ) w₀
      + (potV k w₀ : ℂ) * (Surface.glue u j ∘ Bracket.σ) w₀ = 0 := by
  have hw0 : w₀ ≠ 0 := norm_pos_iff.mp (by rw [heq]; norm_num)
  refine comp_sigma_flat_general hk hw0 ?_ ?_
  · rw [Bracket.σ_self heq]; exact (hu.2.1 j w₀ hmem).of_le two_le_infty
  · rw [Bracket.σ_self heq]; exact glue_flat_jacobi_general hk hu hjac j hmem

/-- Transfer a local flat Jacobi representation through the end chart. -/
lemma endField_laplacian_of_germ_general {k m : ℕ} {u : ZMod (2 * m) → ℂ → ℂ} (p : ℂ)
    (c : ZMod (2 * m)) {ζ : ℂ} (H : ℂ → ℂ)
    (hEq : endFieldWith p u (endIdx m c p) =ᶠ[nhds ζ] fun z => H (endChart p m z))
    (hC2 : ContDiffAt ℝ 2 H (endChart p m ζ))
    (hflat : laplacian H (endChart p m ζ)
      + (potV k (endChart p m ζ) : ℂ) * H (endChart p m ζ) = 0) :
    laplacian (endFieldWith p u (endIdx m c p)) ζ
      + (generalEndPotential k p m ζ : ℂ) * endFieldWith p u (endIdx m c p) ζ = 0 := by
  have hF : endFieldWith p u (endIdx m c p) ζ = H (endChart p m ζ) := hEq.self_of_nhds
  rw [laplacian_congr_of_eventuallyEq hEq, hF]
  exact endComp_of_flat_general k p hC2 hflat

/-- A reflected `C²` Jacobi representation near a seam point away from the argument cut. -/
lemma endField_germ_rep_seam_offCut_general {k m : ℕ} (hk : 2 ≤ k) (p : ℂ)
    {u : ZMod (2 * m) → ℂ → ℂ} (hp : ‖p‖ = 1) (hu : IsSmooth k m u) (hjac : IsJacobiField k m u)
    (hsv : SeamVal k u) (c : ZMod (2 * m)) {ζ₀ : ℂ} {N : ℤ} (hζ₀ : ζ₀ ≠ 0)
    (hcut : 0 < ζ₀.re ∨ ζ₀.im ≠ 0) (hb0 : ‖ζ₀‖ ^ m < 2)
    (hH0 : angT p m ζ₀ - angA m ζ₀ - 2 * Real.pi * (N : ℝ) = 0)
    (hmem0 : endChart p m ζ₀ ∈ seamArc k m (c + 2 * (N : ZMod (2 * m)) - 1)) :
    ∃ H : ℂ → ℂ, (endFieldWith p u (endIdx m c p) =ᶠ[nhds ζ₀] fun z => H (endChart p m z))
      ∧ ContDiffAt ℝ 2 H (endChart p m ζ₀)
      ∧ laplacian H (endChart p m ζ₀) + (potV k (endChart p m ζ₀) : ℂ) * H (endChart p m ζ₀) = 0 := by
  have hendcont : ContinuousAt (endChart p m) ζ₀ := (contDiffAt_endChart p m ζ₀).continuousAt
  have hA : ContinuousAt (fun ζ => angA m ζ) ζ₀ :=
    Real.continuous_arccos.continuousAt.comp
      (((continuous_norm.pow m).continuousAt).neg.div_const 2)
  have hT : ContinuousAt (fun ζ => angT p m ζ) ζ₀ :=
    ((Complex.continuousAt_arg hcut).const_mul (m : ℝ)).sub continuousAt_const
  have hH : ContinuousAt (fun ζ => angT p m ζ - angA m ζ - 2 * Real.pi * (N : ℝ)) ζ₀ :=
    (hT.sub hA).sub continuousAt_const
  have hseam0 : ‖endChart p m ζ₀‖ = 1 := norm_endChart_eq_one hp hb0.le hH0
  have hne0 : endChart p m ζ₀ ≠ 0 := norm_pos_iff.mp (by rw [hseam0]; norm_num)
  have hAmem := angA_mem hζ₀ hb0
  have hA0 : angA m ζ₀ ∈ Set.Ioo 0 Real.pi := ⟨by linarith [Real.pi_pos, hAmem.1], hAmem.2⟩
  have fne : ∀ᶠ ζ in nhds ζ₀, endChart p m ζ ≠ 0 := hendcont.eventually_ne hne0
  have fζ : ∀ᶠ ζ in nhds ζ₀, ζ ≠ 0 := isOpen_ne.mem_nhds hζ₀
  have fb : ∀ᶠ ζ in nhds ζ₀, ‖ζ‖ ^ m ≤ 2 := by
    filter_upwards [(continuous_norm.pow m).continuousAt.eventually_lt continuousAt_const hb0]
      with ζ h using h.le
  have fHbd : ∀ᶠ ζ in nhds ζ₀, -(2 * Real.pi) < angT p m ζ - angA m ζ - 2 * Real.pi * (N : ℝ)
      ∧ angT p m ζ - angA m ζ - 2 * Real.pi * (N : ℝ) < 2 * Real.pi := by
    have hmem : Set.Ioo (-(2 * Real.pi)) (2 * Real.pi)
        ∈ nhds (angT p m ζ₀ - angA m ζ₀ - 2 * Real.pi * (N : ℝ)) := by
      rw [hH0]; exact Ioo_mem_nhds (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos])
    filter_upwards [hH.eventually hmem] with ζ h using ⟨h.1, h.2⟩
  have fAint : ∀ᶠ ζ in nhds ζ₀, 0 ≤ angA m ζ ∧ angA m ζ ≤ Real.pi
      ∧ 0 ≤ angA m ζ + (angT p m ζ - angA m ζ - 2 * Real.pi * (N : ℝ))
      ∧ angA m ζ + (angT p m ζ - angA m ζ - 2 * Real.pi * (N : ℝ)) ≤ Real.pi := by
    have hmemA : Set.Ioo 0 Real.pi ∈ nhds (angA m ζ₀) := Ioo_mem_nhds hA0.1 hA0.2
    have hmemAH : Set.Ioo 0 Real.pi
        ∈ nhds (angA m ζ₀ + (angT p m ζ₀ - angA m ζ₀ - 2 * Real.pi * (N : ℝ))) := by
      have hval : angA m ζ₀ + (angT p m ζ₀ - angA m ζ₀ - 2 * Real.pi * (N : ℝ)) = angA m ζ₀ := by
        rw [hH0]; ring
      rw [hval]; exact Ioo_mem_nhds hA0.1 hA0.2
    filter_upwards [hA.eventually hmemA, (hA.add hH).eventually hmemAH] with ζ hfa hfah
    exact ⟨hfa.1.le, hfa.2.le, hfah.1.le, hfah.2.le⟩
  have farc : ∀ᶠ ζ in nhds ζ₀, ‖endChart p m ζ‖ = 1 →
      endChart p m ζ ∈ seamArc k m (c + 2 * (N : ZMod (2 * m)) - 1) := by
    have hsign0 : (-1 : ℝ) ^ (parity m (c + 2 * (N : ZMod (2 * m)) - 1 + 1)).val
        * ((endChart p m ζ₀) ^ k).re < 0 := by
      have h := hmem0; simp only [seamArc, arc, Set.mem_ofPred_eq] at h; exact h.2
    have hgcont : ContinuousAt (fun ζ => (-1 : ℝ) ^ (parity m (c + 2 * (N : ZMod (2 * m)) - 1 + 1)).val
        * ((endChart p m ζ) ^ k).re) ζ₀ :=
      continuousAt_const.mul (Complex.continuous_re.continuousAt.comp (hendcont.pow k))
    filter_upwards [hgcont.eventually_lt continuousAt_const hsign0] with ζ hg hnorm
    simp only [seamArc, arc, Set.mem_ofPred_eq]
    exact ⟨hnorm, hg⟩
  exact ⟨Surface.glue u (c + 2 * (N : ZMod (2 * m)) - 1) ∘ Bracket.σ,
    endFieldWith_reflected_eventuallyEq_general p hp hsv c fne fζ fb fHbd fAint farc,
    reflectedGerm_contDiffAt_general hu (c + 2 * (N : ZMod (2 * m)) - 1) hmem0 hseam0,
    reflectedGerm_flat_general hk hu hjac (c + 2 * (N : ZMod (2 * m)) - 1) hmem0 hseam0⟩

/-- A locally constant sheet index supplies a direct `C²` Jacobi representation. -/
lemma endField_germ_rep_direct_general {k m : ℕ} {u : ZMod (2 * m) → ℂ → ℂ} (p : ℂ)
    (c : ZMod (2 * m)) {ζ : ℂ}
    (hidx : ∀ᶠ ζ' in nhds ζ, endIdx m c p ζ' = endIdx m c p ζ)
    (hC2 : ContDiffAt ℝ 2 (Surface.glue u (endIdx m c p ζ)) (endChart p m ζ))
    (hflat : laplacian (Surface.glue u (endIdx m c p ζ)) (endChart p m ζ)
      + (potV k (endChart p m ζ) : ℂ) * Surface.glue u (endIdx m c p ζ) (endChart p m ζ) = 0) :
    ∃ H : ℂ → ℂ, (endFieldWith p u (endIdx m c p) =ᶠ[nhds ζ] fun z => H (endChart p m z))
      ∧ ContDiffAt ℝ 2 H (endChart p m ζ)
      ∧ laplacian H (endChart p m ζ) + (potV k (endChart p m ζ) : ℂ) * H (endChart p m ζ) = 0 := by
  refine ⟨Surface.glue u (endIdx m c p ζ), ?_, hC2, hflat⟩
  filter_upwards [hidx] with z hz
  simp only [endFieldWith, hz]

/-- A reflected `C²` Jacobi representation obtained using a continuous argument lift. -/
lemma endField_germ_rep_seam_lift_general {k m : ℕ} (hk : 2 ≤ k) (p : ℂ)
    {u : ZMod (2 * m) → ℂ → ℂ} (hp : ‖p‖ = 1) (hu : IsSmooth k m u) (hjac : IsJacobiField k m u)
    (hsv : SeamVal k u) (c : ZMod (2 * m)) {ζ₀ : ℂ} {N : ℤ} (θ : ℂ → ℝ) (hθc : ContinuousAt θ ζ₀)
    (hθq : ∀ᶠ ζ in nhds ζ₀, ∃ q : ℤ, θ ζ = Complex.arg ζ + 2 * Real.pi * (q : ℝ))
    (hζ₀ : ζ₀ ≠ 0) (hb0 : ‖ζ₀‖ ^ m < 2)
    (hH0 : (m : ℝ) * θ ζ₀ - Complex.arg p - angA m ζ₀ - 2 * Real.pi * (N : ℝ) = 0)
    (hmem0 : endChart p m ζ₀ ∈ seamArc k m (c + 2 * (N : ZMod (2 * m)) - 1)) :
    ∃ H : ℂ → ℂ, (endFieldWith p u (endIdx m c p) =ᶠ[nhds ζ₀] fun z => H (endChart p m z))
      ∧ ContDiffAt ℝ 2 H (endChart p m ζ₀)
      ∧ laplacian H (endChart p m ζ₀) + (potV k (endChart p m ζ₀) : ℂ) * H (endChart p m ζ₀) = 0 := by
  obtain ⟨q0, hq0⟩ := hθq.self_of_nhds
  have hcs0 : Real.cos ((m : ℝ) * θ ζ₀ - Complex.arg p) = Real.cos (angT p m ζ₀) := cos_lift_eq hq0
  have hseam0 : ‖endChart p m ζ₀‖ = 1 := norm_endChart_eq_one_gen hp hb0.le hcs0 hH0
  have hne0 : endChart p m ζ₀ ≠ 0 := norm_pos_iff.mp (by rw [hseam0]; norm_num)
  have hendcont : ContinuousAt (endChart p m) ζ₀ := (contDiffAt_endChart p m ζ₀).continuousAt
  have hA : ContinuousAt (fun ζ => angA m ζ) ζ₀ :=
    Real.continuous_arccos.continuousAt.comp
      (((continuous_norm.pow m).continuousAt).neg.div_const 2)
  have hH : ContinuousAt
      (fun ζ => (m : ℝ) * θ ζ - Complex.arg p - angA m ζ - 2 * Real.pi * (N : ℝ)) ζ₀ :=
    (((hθc.const_mul (m : ℝ)).sub continuousAt_const).sub hA).sub continuousAt_const
  have hAmem := angA_mem hζ₀ hb0
  have hA0 : angA m ζ₀ ∈ Set.Ioo 0 Real.pi := ⟨by linarith [Real.pi_pos, hAmem.1], hAmem.2⟩
  have fne : ∀ᶠ ζ in nhds ζ₀, endChart p m ζ ≠ 0 := hendcont.eventually_ne hne0
  have fζ : ∀ᶠ ζ in nhds ζ₀, ζ ≠ 0 := isOpen_ne.mem_nhds hζ₀
  have hb : ∀ᶠ ζ in nhds ζ₀, ‖ζ‖ ^ m ≤ 2 := by
    filter_upwards [(continuous_norm.pow m).continuousAt.eventually_lt continuousAt_const hb0]
      with ζ h using h.le
  have fHbd : ∀ᶠ ζ in nhds ζ₀, -(2 * Real.pi) < (m : ℝ) * θ ζ - Complex.arg p - angA m ζ
      - 2 * Real.pi * (N : ℝ) ∧ (m : ℝ) * θ ζ - Complex.arg p - angA m ζ
      - 2 * Real.pi * (N : ℝ) < 2 * Real.pi := by
    have hmem : Set.Ioo (-(2 * Real.pi)) (2 * Real.pi)
        ∈ nhds ((m : ℝ) * θ ζ₀ - Complex.arg p - angA m ζ₀ - 2 * Real.pi * (N : ℝ)) := by
      rw [hH0]; exact Ioo_mem_nhds (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos])
    filter_upwards [hH.eventually hmem] with ζ h using ⟨h.1, h.2⟩
  have fAint : ∀ᶠ ζ in nhds ζ₀, 0 ≤ angA m ζ ∧ angA m ζ ≤ Real.pi
      ∧ 0 ≤ angA m ζ + ((m : ℝ) * θ ζ - Complex.arg p - angA m ζ - 2 * Real.pi * (N : ℝ))
      ∧ angA m ζ + ((m : ℝ) * θ ζ - Complex.arg p - angA m ζ - 2 * Real.pi * (N : ℝ)) ≤ Real.pi := by
    have hmemA : Set.Ioo 0 Real.pi ∈ nhds (angA m ζ₀) := Ioo_mem_nhds hA0.1 hA0.2
    have hmemAH : Set.Ioo 0 Real.pi ∈ nhds (angA m ζ₀ + ((m : ℝ) * θ ζ₀ - Complex.arg p
        - angA m ζ₀ - 2 * Real.pi * (N : ℝ))) := by
      have hval : angA m ζ₀ + ((m : ℝ) * θ ζ₀ - Complex.arg p - angA m ζ₀ - 2 * Real.pi * (N : ℝ))
          = angA m ζ₀ := by rw [hH0]; ring
      rw [hval]; exact Ioo_mem_nhds hA0.1 hA0.2
    filter_upwards [hA.eventually hmemA, (hA.add hH).eventually hmemAH] with ζ hfa hfah
    exact ⟨hfa.1.le, hfa.2.le, hfah.1.le, hfah.2.le⟩
  have farc : ∀ᶠ ζ in nhds ζ₀, ‖endChart p m ζ‖ = 1 →
      endChart p m ζ ∈ seamArc k m (c + 2 * (N : ZMod (2 * m)) - 1) := by
    have hsign0 : (-1 : ℝ) ^ (parity m (c + 2 * (N : ZMod (2 * m)) - 1 + 1)).val
        * ((endChart p m ζ₀) ^ k).re < 0 := by
      have h := hmem0; simp only [seamArc, arc, Set.mem_ofPred_eq] at h; exact h.2
    have hgcont : ContinuousAt (fun ζ => (-1 : ℝ) ^ (parity m (c + 2 * (N : ZMod (2 * m)) - 1 + 1)).val
        * ((endChart p m ζ) ^ k).re) ζ₀ :=
      continuousAt_const.mul (Complex.continuous_re.continuousAt.comp (hendcont.pow k))
    filter_upwards [hgcont.eventually_lt continuousAt_const hsign0] with ζ hg hnorm
    simp only [seamArc, arc, Set.mem_ofPred_eq]
    exact ⟨hnorm, hg⟩
  exact ⟨Surface.glue u (c + 2 * (N : ZMod (2 * m)) - 1) ∘ Bracket.σ,
    endFieldWith_reflected_eventuallyEq_lift_general p hp hsv c θ hθq fne fζ hb fHbd fAint farc,
    reflectedGerm_contDiffAt_general hu (c + 2 * (N : ZMod (2 * m)) - 1) hmem0 hseam0,
    reflectedGerm_flat_general hk hu hjac (c + 2 * (N : ZMod (2 * m)) - 1) hmem0 hseam0⟩

/-! ### The complex equation and its real and imaginary parts

The interior, seam and exterior cases provide local representations.
The argument-cut cases use a continuous lift. Each point retains the
positivity hypothesis on `Re(Sk k q)`. -/

/-- The end-field Jacobi equation away from the principal argument cut. -/
lemma endField_laplacian_offCut_general {k m : ℕ} (hk : 2 ≤ k) {u : ZMod (2 * m) → ℂ → ℂ} (p : ℂ)
    (hp : ‖p‖ = 1) (hpunc : p ∈ punctures k) (hu : IsSmooth k m u) (hjac : IsJacobiField k m u)
    (hsv : SeamVal k u) (c : ZMod (2 * m)) {ζ : ℂ} (hcut : 0 < ζ.re ∨ ζ.im ≠ 0) (hζ : ζ ≠ 0)
    (hρ1 : ‖ζ‖ ^ m < 1) (hbit : 0 < (-1 : ℝ) ^ (parity m c).val * (p ^ k).im)
    (hS : 0 < (Sk k ((starRingEnd ℂ) p * endChart p m ζ)).re) :
    laplacian (endFieldWith p u (endIdx m c p)) ζ
      + (generalEndPotential k p m ζ : ℂ) * endFieldWith p u (endIdx m c p) ζ = 0 := by
  have hρ2 : ‖ζ‖ ^ m < 2 := lt_trans hρ1 one_lt_two
  have hnsOff : ‖endChart p m ζ‖ ≠ 1 →
      ∀ᶠ ζ' in nhds ζ, endIdx m c p ζ' = endIdx m c p ζ := by
    intro hne1
    have hns : ∀ i : ℤ, (angT p m ζ - angA m ζ) / (2 * Real.pi) ≠ (i : ℝ) := by
      intro i hi
      rw [div_eq_iff (by positivity)] at hi
      have hcos : Real.cos (angT p m ζ) = Real.cos (angA m ζ) := by
        rw [show angT p m ζ = angA m ζ + (i : ℝ) * (2 * Real.pi) from by linarith [hi],
          Real.cos_add_int_mul_two_pi]
      have h := endChart_normSq_sub_one_cos hp hρ2.le
      rw [hcos, sub_self, mul_zero] at h
      have hsq : ‖endChart p m ζ‖ ^ 2 = 1 := by rw [Complex.sq_norm]; linarith
      exact hne1 (by rw [← Real.sqrt_sq (norm_nonneg _), hsq, Real.sqrt_one])
    filter_upwards [angJ_eventuallyEq hcut hns] with ζ' h; simp only [endIdx, h]
  rcases lt_trichotomy (‖endChart p m ζ‖) 1 with hlt | heq | hgt
  · obtain ⟨H, hEq, hC2, hflat⟩ := endField_germ_rep_direct_general p c (hnsOff (ne_of_lt hlt))
      (glue_contDiffAt_disk hu.1 (endIdx m c p ζ) hlt)
      (glue_flat_disk_general hk hjac (endIdx m c p ζ) hlt)
    exact endField_laplacian_of_germ_general p c H hEq hC2 hflat
  · have hcosT : Real.cos (angT p m ζ) = Real.cos (angA m ζ) := by
      have h := endChart_normSq_sub_one_cos hp hρ2.le
      have hns1 : Complex.normSq (endChart p m ζ) = 1 := by
        rw [Complex.normSq_eq_norm_sq, heq]; norm_num
      rw [hns1] at h
      have h0 : 2 * ‖ζ‖ ^ m * (Real.cos (angT p m ζ) - Real.cos (angA m ζ)) = 0 := by linarith [h]
      rcases mul_eq_zero.mp h0 with h' | h'
      · exact absurd h' (by positivity)
      · linarith [h']
    have hAmem := angA_mem hζ hρ2
    rw [Real.cos_eq_cos_iff] at hcosT
    obtain ⟨j, hj | hj⟩ := hcosT
    · have hT2 : angT p m ζ = angA m ζ + ((-j : ℤ) : ℝ) * (2 * Real.pi) := by
        push_cast; linear_combination -hj
      have hH0 : angT p m ζ - angA m ζ - 2 * Real.pi * (((-j : ℤ)) : ℝ) = 0 := by rw [hT2]; ring
      have hsinT : 0 < Real.sin (angT p m ζ) := by
        rw [hT2, Real.sin_add_int_mul_two_pi]
        exact Real.sin_pos_of_pos_of_lt_pi (by linarith [hAmem.1, Real.pi_pos]) hAmem.2
      have hQ : 0 < (((starRingEnd ℂ) p * endChart p m ζ) ^ k).im := q_imKpow_pos hp hζ hsinT hS
      obtain ⟨H, hEq, hC2, hflat⟩ := endField_germ_rep_seam_offCut_general hk p hp hu hjac hsv c
        hζ hcut hρ2 hH0 (arc_mem_of_imKpow_pos hpunc hp heq hQ (by rw [parity_add_two_mul]; exact hbit))
      exact endField_laplacian_of_germ_general p c H hEq hC2 hflat
    · have hT2 : angT p m ζ = -angA m ζ + ((j : ℤ) : ℝ) * (2 * Real.pi) := by
        linear_combination hj
      have hsinT : Real.sin (angT p m ζ) < 0 := by
        rw [hT2, Real.sin_add_int_mul_two_pi, Real.sin_neg]
        have := Real.sin_pos_of_pos_of_lt_pi (show 0 < angA m ζ by linarith [hAmem.1, Real.pi_pos])
          hAmem.2
        linarith
      have hns : ∀ i : ℤ, (angT p m ζ - angA m ζ) / (2 * Real.pi) ≠ (i : ℝ) := by
        intro i hi
        rw [div_eq_iff (by positivity)] at hi
        rw [hT2] at hi
        have hApi : angA m ζ = ((j : ℝ) - (i : ℝ)) * Real.pi := by
          linear_combination (-1 / 2 : ℝ) * hi
        rw [hApi] at hAmem
        have hlo : (1 : ℝ) / 2 < (j : ℝ) - (i : ℝ) := by nlinarith [hAmem.1, Real.pi_pos]
        have hhi : (j : ℝ) - (i : ℝ) < 1 := by nlinarith [hAmem.2, Real.pi_pos]
        have hlo' : (0 : ℤ) < j - i := by
          have hh : (0 : ℝ) < ((j - i : ℤ) : ℝ) := by push_cast; linarith [hlo]
          exact_mod_cast hh
        have hhi' : (j - i : ℤ) < 1 := by
          have hh : ((j - i : ℤ) : ℝ) < 1 := by push_cast; linarith [hhi]
          exact_mod_cast hh
        omega
      have hidx : ∀ᶠ ζ' in nhds ζ, endIdx m c p ζ' = endIdx m c p ζ := by
        filter_upwards [angJ_eventuallyEq hcut hns] with ζ' h; simp only [endIdx, h]
      have hpe : parity m (endIdx m c p ζ + 1) = parity m c + 1 := by
        simp only [endIdx]; rw [map_add, map_one, parity_add_two_mul]
      have hpar : (-1 : ℝ) ^ (parity m (endIdx m c p ζ + 1)).val * (p ^ k).im < 0 := by
        rw [hpe, neg_one_pow_parity_add_one]; nlinarith [hbit]
      have hQ : (((starRingEnd ℂ) p * endChart p m ζ) ^ k).im < 0 := q_imKpow_neg hp hζ hsinT hS
      have harc := arc_mem_of_imKpow_neg hpunc hp heq hQ hpar
      obtain ⟨H, hEq, hC2, hflat⟩ := endField_germ_rep_direct_general p c hidx
        ((hu.2.1 (endIdx m c p ζ) (endChart p m ζ) harc).of_le two_le_infty)
        (glue_flat_jacobi_general hk hu hjac (endIdx m c p ζ) harc)
      exact endField_laplacian_of_germ_general p c H hEq hC2 hflat
  · obtain ⟨H, hEq, hC2, hflat⟩ := endField_germ_rep_direct_general p c (hnsOff (ne_of_gt hgt))
      (glue_contDiffAt_exterior hu.1 (endIdx m c p ζ) hgt)
      (glue_flat_exterior_general hk hu.1 hjac (endIdx m c p ζ) hgt)
    exact endField_laplacian_of_germ_general p c H hEq hC2 hflat

/-- The end-field Jacobi equation using a continuous argument lift. -/
lemma endField_laplacian_cut_general {k m : ℕ} (hk : 2 ≤ k) {u : ZMod (2 * m) → ℂ → ℂ} (p : ℂ)
    (hp : ‖p‖ = 1) (hpunc : p ∈ punctures k) (hu : IsSmooth k m u) (hjac : IsJacobiField k m u)
    (hsv : SeamVal k u) (c : ZMod (2 * m)) {ζ₀ : ℂ} (hcre : ζ₀.re < 0) (hρ1 : ‖ζ₀‖ ^ m < 1)
    (hbit : 0 < (-1 : ℝ) ^ (parity m c).val * (p ^ k).im)
    (hS : 0 < (Sk k ((starRingEnd ℂ) p * endChart p m ζ₀)).re) :
    laplacian (endFieldWith p u (endIdx m c p)) ζ₀
      + (generalEndPotential k p m ζ₀ : ℂ) * endFieldWith p u (endIdx m c p) ζ₀ = 0 := by
  have hζ₀ : ζ₀ ≠ 0 := fun h => by simp [h] at hcre
  have hρ2 : ‖ζ₀‖ ^ m < 2 := lt_trans hρ1 one_lt_two
  set θ : ℂ → ℝ := fun ζ => Complex.arg (-ζ) + Real.pi with hθdef
  have hθc : ContinuousAt θ ζ₀ := argLift_continuousAt (Or.inl hcre)
  have hθq : ∀ᶠ ζ in nhds ζ₀, ∃ q : ℤ, θ ζ = Complex.arg ζ + 2 * Real.pi * (q : ℝ) := by
    filter_upwards [isOpen_ne.mem_nhds hζ₀] with ζ hζ using argLift_arg_eq hζ
  obtain ⟨q0, hq0⟩ := hθq.self_of_nhds
  have hcs0 : Real.cos ((m : ℝ) * θ ζ₀ - Complex.arg p) = Real.cos (angT p m ζ₀) := cos_lift_eq hq0
  have hsn0 : Real.sin ((m : ℝ) * θ ζ₀ - Complex.arg p) = Real.sin (angT p m ζ₀) := sin_lift_eq hq0
  rcases lt_trichotomy (‖endChart p m ζ₀‖) 1 with hlt | heq | hgt
  · have hns : ∀ i : ℤ, ((m : ℝ) * θ ζ₀ - Complex.arg p - angA m ζ₀) / (2 * Real.pi) ≠ (i : ℝ) := by
      intro i hi
      rw [div_eq_iff (by positivity)] at hi
      have hH0k : (m : ℝ) * θ ζ₀ - Complex.arg p - angA m ζ₀ - 2 * Real.pi * (i : ℝ) = 0 := by
        linear_combination hi
      rw [norm_endChart_eq_one_gen hp hρ2.le hcs0 hH0k] at hlt; exact lt_irrefl 1 hlt
    obtain ⟨H, hEq, hC2, hflat⟩ := endField_germ_rep_direct_general p c
      (endIdx_eventuallyEq_of_lift θ hθc hθq hns)
      (glue_contDiffAt_disk hu.1 (endIdx m c p ζ₀) hlt)
      (glue_flat_disk_general hk hjac (endIdx m c p ζ₀) hlt)
    exact endField_laplacian_of_germ_general p c H hEq hC2 hflat
  · have hcosT : Real.cos (angT p m ζ₀) = Real.cos (angA m ζ₀) := by
      have h := endChart_normSq_sub_one_cos hp hρ2.le
      have hns1 : Complex.normSq (endChart p m ζ₀) = 1 := by
        rw [Complex.normSq_eq_norm_sq, heq]; norm_num
      rw [hns1] at h
      have h0 : 2 * ‖ζ₀‖ ^ m * (Real.cos (angT p m ζ₀) - Real.cos (angA m ζ₀)) = 0 := by linarith [h]
      rcases mul_eq_zero.mp h0 with h' | h'
      · exact absurd h' (by positivity)
      · linarith [h']
    have hAmem := angA_mem hζ₀ hρ2
    have hcosS : Real.cos ((m : ℝ) * θ ζ₀ - Complex.arg p) = Real.cos (angA m ζ₀) := by
      rw [hcs0, hcosT]
    rw [Real.cos_eq_cos_iff] at hcosS
    obtain ⟨j, hj | hj⟩ := hcosS
    · have hH0 : (m : ℝ) * θ ζ₀ - Complex.arg p - angA m ζ₀ - 2 * Real.pi * (((-j : ℤ)) : ℝ) = 0 := by
        push_cast; linear_combination -hj
      have hsinT : 0 < Real.sin (angT p m ζ₀) := by
        rw [← hsn0, show (m : ℝ) * θ ζ₀ - Complex.arg p
            = angA m ζ₀ + ((-j : ℤ) : ℝ) * (2 * Real.pi) from by push_cast; linear_combination -hj,
          Real.sin_add_int_mul_two_pi]
        exact Real.sin_pos_of_pos_of_lt_pi (by linarith [hAmem.1, Real.pi_pos]) hAmem.2
      have hQ : 0 < (((starRingEnd ℂ) p * endChart p m ζ₀) ^ k).im := q_imKpow_pos hp hζ₀ hsinT hS
      have hmem0 : endChart p m ζ₀ ∈ seamArc k m (c + 2 * (((-j : ℤ)) : ZMod (2 * m)) - 1) :=
        arc_mem_of_imKpow_pos hpunc hp heq hQ (by rw [parity_add_two_mul]; exact hbit)
      obtain ⟨H, hEq, hC2, hflat⟩ :=
        endField_germ_rep_seam_lift_general hk p hp hu hjac hsv c θ hθc hθq hζ₀ hρ2 hH0 hmem0
      exact endField_laplacian_of_germ_general p c H hEq hC2 hflat
    · have hsS : (m : ℝ) * θ ζ₀ - Complex.arg p = -angA m ζ₀ + ((j : ℤ) : ℝ) * (2 * Real.pi) := by
        linear_combination hj
      have hsinT : Real.sin (angT p m ζ₀) < 0 := by
        rw [← hsn0, hsS, Real.sin_add_int_mul_two_pi, Real.sin_neg]
        have := Real.sin_pos_of_pos_of_lt_pi (show 0 < angA m ζ₀ by linarith [hAmem.1, Real.pi_pos])
          hAmem.2
        linarith
      have hns : ∀ i : ℤ, ((m : ℝ) * θ ζ₀ - Complex.arg p - angA m ζ₀) / (2 * Real.pi) ≠ (i : ℝ) := by
        intro i hi
        rw [div_eq_iff (by positivity)] at hi
        rw [hsS] at hi
        have hApi : angA m ζ₀ = ((j : ℝ) - (i : ℝ)) * Real.pi := by
          linear_combination (-1 / 2 : ℝ) * hi
        rw [hApi] at hAmem
        have hlo : (1 : ℝ) / 2 < (j : ℝ) - (i : ℝ) := by nlinarith [hAmem.1, Real.pi_pos]
        have hhi : (j : ℝ) - (i : ℝ) < 1 := by nlinarith [hAmem.2, Real.pi_pos]
        have hlo' : (0 : ℤ) < j - i := by
          have hh : (0 : ℝ) < ((j - i : ℤ) : ℝ) := by push_cast; linarith [hlo]
          exact_mod_cast hh
        have hhi' : (j - i : ℤ) < 1 := by
          have hh : ((j - i : ℤ) : ℝ) < 1 := by push_cast; linarith [hhi]
          exact_mod_cast hh
        omega
      have hpe : parity m (endIdx m c p ζ₀ + 1) = parity m c + 1 := by
        simp only [endIdx]; rw [map_add, map_one, parity_add_two_mul]
      have hpar : (-1 : ℝ) ^ (parity m (endIdx m c p ζ₀ + 1)).val * (p ^ k).im < 0 := by
        rw [hpe, neg_one_pow_parity_add_one]; nlinarith [hbit]
      have hQ : (((starRingEnd ℂ) p * endChart p m ζ₀) ^ k).im < 0 := q_imKpow_neg hp hζ₀ hsinT hS
      have harc := arc_mem_of_imKpow_neg hpunc hp heq hQ hpar
      obtain ⟨H, hEq, hC2, hflat⟩ := endField_germ_rep_direct_general p c
        (endIdx_eventuallyEq_of_lift θ hθc hθq hns)
        ((hu.2.1 (endIdx m c p ζ₀) (endChart p m ζ₀) harc).of_le two_le_infty)
        (glue_flat_jacobi_general hk hu hjac (endIdx m c p ζ₀) harc)
      exact endField_laplacian_of_germ_general p c H hEq hC2 hflat
  · have hns : ∀ i : ℤ, ((m : ℝ) * θ ζ₀ - Complex.arg p - angA m ζ₀) / (2 * Real.pi) ≠ (i : ℝ) := by
      intro i hi
      rw [div_eq_iff (by positivity)] at hi
      have hH0k : (m : ℝ) * θ ζ₀ - Complex.arg p - angA m ζ₀ - 2 * Real.pi * (i : ℝ) = 0 := by
        linear_combination hi
      rw [norm_endChart_eq_one_gen hp hρ2.le hcs0 hH0k] at hgt; exact lt_irrefl 1 hgt
    obtain ⟨H, hEq, hC2, hflat⟩ := endField_germ_rep_direct_general p c
      (endIdx_eventuallyEq_of_lift θ hθc hθq hns)
      (glue_contDiffAt_exterior hu.1 (endIdx m c p ζ₀) hgt)
      (glue_flat_exterior_general hk hu.1 hjac (endIdx m c p ζ₀) hgt)
    exact endField_laplacian_of_germ_general p c H hEq hC2 hflat

/-- The complex Jacobi equation at nonzero chart points satisfying the radius and polynomial positivity hypotheses. -/
theorem endField_laplacian_punctured_general {k m : ℕ} (hk : 2 ≤ k) {u : ZMod (2 * m) → ℂ → ℂ}
    (p : ℂ) (hp : ‖p‖ = 1) (hpunc : p ∈ punctures k) (hu : IsSmooth k m u)
    (hjac : IsJacobiField k m u) (hsv : SeamVal k u) (c : ZMod (2 * m))
    (hbit : 0 < (-1 : ℝ) ^ (parity m c).val * (p ^ k).im) :
    ∀ ζ : ℂ, ζ ≠ 0 → ‖ζ‖ ^ m < 1 → 0 < (Sk k ((starRingEnd ℂ) p * endChart p m ζ)).re →
      laplacian (endFieldWith p u (endIdx m c p)) ζ
        + (generalEndPotential k p m ζ : ℂ) * endFieldWith p u (endIdx m c p) ζ = 0 := by
  intro ζ hζ hρ1 hS
  by_cases hcut : 0 < ζ.re ∨ ζ.im ≠ 0
  · exact endField_laplacian_offCut_general hk p hp hpunc hu hjac hsv c hcut hζ hρ1 hbit hS
  · rw [not_or, not_lt, not_ne_iff] at hcut
    have hcre : ζ.re < 0 := lt_of_le_of_ne hcut.1
      (fun h => hζ (Complex.ext (by rw [Complex.zero_re]; exact h)
        (by rw [Complex.zero_im]; exact hcut.2)))
    exact endField_laplacian_cut_general hk p hp hpunc hu hjac hsv c hcre hρ1 hbit hS

/-- Neighborhood `C²` of the end field, general `k` (builds the `S_k`-positivity neighborhood from
`hS` at `ζ` by continuity of `Re(S_k(conj p·endChart ·))`). -/
lemma endField_eventually_contDiffAt_general {k m : ℕ} {u : ZMod (2 * m) → ℂ → ℂ} (p : ℂ)
    (hp : ‖p‖ = 1) (hpunc : p ∈ punctures k) (hu : IsSmooth k m u) (hsv : SeamVal k u)
    (c : ZMod (2 * m)) (hbit : 0 < (-1 : ℝ) ^ (parity m c).val * (p ^ k).im) {ζ : ℂ} (hζ : ζ ≠ 0)
    (hρ1 : ‖ζ‖ ^ m < 1) (hS : 0 < (Sk k ((starRingEnd ℂ) p * endChart p m ζ)).re) :
    ∀ᶠ y in nhds ζ, ContDiffAt ℝ 2 (endFieldWith p u (endIdx m c p)) y := by
  have hρball : ∀ᶠ y in nhds ζ, ‖y‖ ^ m < 1 := by
    filter_upwards [(continuous_norm.pow m).continuousAt.eventually_lt continuousAt_const hρ1]
      with y h using h
  have hSnhd : ∀ᶠ y in nhds ζ, 0 < (Sk k ((starRingEnd ℂ) p * endChart p m y)).re := by
    have hqc : ContinuousAt (fun y => (starRingEnd ℂ) p * endChart p m y) ζ :=
      continuousAt_const.mul (contDiffAt_endChart p m ζ).continuousAt
    have hcont : ContinuousAt (fun y => (Sk k ((starRingEnd ℂ) p * endChart p m y)).re) ζ :=
      Complex.continuous_re.continuousAt.comp ((continuous_Sk k).continuousAt.comp hqc)
    exact continuousAt_const.eventually_lt hcont hS
  filter_upwards [isOpen_ne.mem_nhds hζ, hρball, hSnhd] with y hy hyρ hyS
  exact endField_contDiffAt_punctured_general p hp hpunc hu hsv c hbit y hy hyρ hyS

/-- The real part of the end field solves the `lapReal` equation. -/
theorem endField_hre_general {k m : ℕ} (hk : 2 ≤ k) {u : ZMod (2 * m) → ℂ → ℂ} (p : ℂ)
    (hp : ‖p‖ = 1) (hpunc : p ∈ punctures k) (hu : IsSmooth k m u) (hjac : IsJacobiField k m u)
    (hsv : SeamVal k u) (c : ZMod (2 * m)) (hbit : 0 < (-1 : ℝ) ^ (parity m c).val * (p ^ k).im) :
    ∀ ζ : ℂ, ζ ≠ 0 → ‖ζ‖ ^ m < 1 → 0 < (Sk k ((starRingEnd ℂ) p * endChart p m ζ)).re →
      lapReal (fun z => (endFieldWith p u (endIdx m c p) z).re) ζ
        + generalEndPotential k p m ζ * (endFieldWith p u (endIdx m c p) ζ).re = 0 := by
  intro ζ hζ hρ1 hS
  rw [lapReal_re (endField_eventually_contDiffAt_general p hp hpunc hu hsv c hbit hζ hρ1 hS)]
  have hlap : laplacian (endFieldWith p u (endIdx m c p)) ζ
      = -(generalEndPotential k p m ζ : ℂ) * endFieldWith p u (endIdx m c p) ζ := by
    linear_combination
      endField_laplacian_punctured_general hk p hp hpunc hu hjac hsv c hbit ζ hζ hρ1 hS
  rw [hlap]
  simp only [Complex.mul_re, Complex.neg_re, Complex.neg_im, Complex.ofReal_re, Complex.ofReal_im]
  ring

/-- The imaginary part of the end field solves the `lapReal` equation. -/
theorem endField_him_general {k m : ℕ} (hk : 2 ≤ k) {u : ZMod (2 * m) → ℂ → ℂ} (p : ℂ)
    (hp : ‖p‖ = 1) (hpunc : p ∈ punctures k) (hu : IsSmooth k m u) (hjac : IsJacobiField k m u)
    (hsv : SeamVal k u) (c : ZMod (2 * m)) (hbit : 0 < (-1 : ℝ) ^ (parity m c).val * (p ^ k).im) :
    ∀ ζ : ℂ, ζ ≠ 0 → ‖ζ‖ ^ m < 1 → 0 < (Sk k ((starRingEnd ℂ) p * endChart p m ζ)).re →
      lapReal (fun z => (endFieldWith p u (endIdx m c p) z).im) ζ
        + generalEndPotential k p m ζ * (endFieldWith p u (endIdx m c p) ζ).im = 0 := by
  intro ζ hζ hρ1 hS
  rw [lapReal_im (endField_eventually_contDiffAt_general p hp hpunc hu hsv c hbit hζ hρ1 hS)]
  have hlap : laplacian (endFieldWith p u (endIdx m c p)) ζ
      = -(generalEndPotential k p m ζ : ℂ) * endFieldWith p u (endIdx m c p) ζ := by
    linear_combination
      endField_laplacian_punctured_general hk p hp hpunc hu hjac hsv c hbit ζ hζ hρ1 hS
  rw [hlap]
  simp only [Complex.mul_im, Complex.neg_re, Complex.neg_im, Complex.ofReal_re, Complex.ofReal_im]
  ring

end KsIndex.EndField
