module

public import KsIndexLean.SmoothSlitCharacterAverage
public import KsIndexLean.PaperSlitBoundedApproximation

@[expose] public section


open Set MeasureTheory Filter Topology
open scoped ContDiff
noncomputable section
namespace KsIndex.Spectral
open KsIndex.Trace KsIndex.WeakH1 KsIndex.Spherical

/-- Smooth representatives on both hemispheres, smooth gluing on both arcs,
and a common puncture hole. The weak carrier retains the phase and character. -/
def PaperSlitSmoothRepresentative (α : ℝ) (j : ℕ)
    (u : paperSlitCharacterDomain α j) : Prop :=
  ∃ f g : ℂ → ℂ, ContDiff ℝ ∞ f ∧ ContDiff ℝ ∞ g ∧
    (valueCLM u.val.1 : ℂ → ℂ) =ᵐ[volume.restrict (disk : Set ℂ)] f ∧
    (valueCLM u.val.2 : ℂ → ℂ) =ᵐ[volume.restrict (disk : Set ℂ)] g ∧
    (∀ b, b = 0 ∨ b = 1 → ∀ z ∈ Surface.arc 3 b,
      ContDiffAt ℝ ∞ (phaseGerm (if b = 0 then paperPhase α else 1)
        (closedDiskRestriction f) (closedDiskRestriction g)) z ∧
      ContDiffAt ℝ ∞ (phaseGerm (if b = 0 then (paperPhase α)⁻¹ else 1)
        (closedDiskRestriction g) (closedDiskRestriction f)) z) ∧
    ∃ δ : ℝ, 0 < δ ∧ ∀ q ∈ Surface.punctures 3, ∀ z,
      ‖z - q‖ < δ → f z = 0 ∧ g z = 0

/-- The paper's smooth slit density, in upper/lower disk coordinates, for
arbitrary real phase. No rationality or finite cyclic extension is assumed. -/
theorem exists_paperSlit_smooth_approx (α : ℝ) (j : ℕ)
    (u : paperSlitCharacterDomain α j) {ε : ℝ} (hε : 0 < ε) :
    ∃ w : paperSlitCharacterDomain α j,
      ‖w.val - u.val‖ < ε ∧ PaperSlitSmoothRepresentative α j w := by
  obtain ⟨v, M, ρ, hM, hρ, hvu, hb1, hb2, hz1, hz2⟩ :=
    exists_paperSlit_puncture_approx α j u (half_pos hε)
  let H : Set ℂ := ⋃ q ∈ Surface.punctures 3, Metric.ball q ρ
  have hH : IsOpen H := isOpen_biUnion (fun q _ => Metric.isOpen_ball)
  have hpH : Surface.punctures 3 ⊆ H :=
    fun q hq => Set.mem_biUnion hq (Metric.mem_ball_self hρ)
  have hzero {v : ComplexH1}
      (h : ∀ᵐ z ∂volume.restrict disk,
        (∃ q ∈ Surface.punctures 3, ‖z - q‖ ≤ ρ) → valueCLM v z = 0) :
      ∀ᵐ z ∂volume.restrict disk, z ∈ H → valueCLM v z = 0 := by
    filter_upwards [h] with z hz hzH
    obtain ⟨q, hq, hqz⟩ := Set.mem_iUnion₂.mp hzH
    exact hz ⟨q, hq, by simpa only [dist_eq_norm] using (Metric.mem_ball.mp hqz).le⟩
  obtain ⟨f, g, U, V, ht, hs⟩ := punctured_slit_pair_approximation (by decide : 1 ≤ 3)
    (paperPhase α) (Complex.exp_ne_zero _) ⟨v.val, v.property.1⟩ hH hpH (hzero hz1) (hzero hz2)
  have ht' := carrierCharProj_pair_tendsto (by decide : 0 < 3) j ht v.property.2
  have he := Metric.tendsto_nhds.mp ht' (ε / 2) (half_pos hε)
  obtain ⟨n, hn, hclose⟩ := (hs.and he).exists
  obtain ⟨hf, hU, hg, hV, hseam, hmem, δ, hδ, hhole⟩ := hn
  let w : paperSlitCharacterDomain α j :=
    ⟨_, carrierCharProj_pair_mem (by decide : 0 < 3) j (paperPhase α) (U n, V n) hmem⟩
  refine ⟨w, ?_, smoothCharacterAverage 3 j (f n), smoothCharacterAverage 3 j (g n),
    smoothCharacterAverage_smooth 3 j hf, smoothCharacterAverage_smooth 3 j hg,
    smoothCharacterAverage_value 3 j hU.1, smoothCharacterAverage_value 3 j hV.1, ?_,
    δ, hδ, ?_⟩
  · have htriangle := norm_add_le (w.val - v.val) (v.val - u.val)
    have hc : ‖w.val - v.val‖ < ε / 2 := by simpa only [dist_eq_norm] using hclose
    rw [sub_add_sub_cancel] at htriangle
    linarith
  · intro b hb z hz
    exact ⟨smoothCharacterAverage_seam (by decide : 0 < 3) j b _
      (fun z hz => (hseam b hb z hz).1) z hz,
      smoothCharacterAverage_seam (by decide : 0 < 3) j b _
      (fun z hz => (hseam b hb z hz).2) z hz⟩
  · intro q hq z hz
    exact ⟨smoothCharacterAverage_holes (by decide : 0 < 3) j (f n)
      (fun q hq z hz => (hhole q hq z hz).1) q hq z hz,
      smoothCharacterAverage_holes (by decide : 0 < 3) j (g n)
      (fun q hq z hz => (hhole q hq z hz).2) q hq z hz⟩

/-- The smooth, puncture-avoiding representatives are dense in every real
phase and rotation character of the weak slit space. -/
theorem paperSlit_smooth_dense (α : ℝ) (j : ℕ) :
    Dense {u : paperSlitCharacterDomain α j | PaperSlitSmoothRepresentative α j u} := by
  rw [Metric.dense_iff]
  intro u ε hε
  obtain ⟨w, hw, hs⟩ := exists_paperSlit_smooth_approx α j u hε
  refine ⟨w, ?_, hs⟩
  change dist w.val u.val < ε
  rw [dist_eq_norm]
  exact hw

end KsIndex.Spectral
