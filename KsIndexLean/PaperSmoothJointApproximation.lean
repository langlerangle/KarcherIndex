module

public import KsIndexLean.CcSmoothCharacterAverage
public import KsIndexLean.PaperSmoothChainSector
public import KsIndexLean.PaperSlitBoundedApproximation

@[expose] public section


open Set MeasureTheory Filter Topology
noncomputable section
namespace KsIndex.Spectral
open KsIndex.Trace KsIndex.WeakH1 KsIndex.Spherical

/-- Package an original smooth family with the two exact paper symmetries. -/
def paperSmoothJointOfFamily (m n j : ℕ) (u : Surface.CcSmooth 3 m)
    (hp : ∀ q z, u.val (q + 2) z = paperPhase ((n : ℝ) / m) * u.val q z)
    (hr : Surface.uncurryE m u.val ∈ Module.End.eigenspace
      (SurfaceSym.rotE m (Complex.exp (((-(2 * Real.pi) / 3 : ℝ) : ℂ) * Complex.I)))
        (KsIndex.FormIndex.zeta 3 ^ j)) : paperSmoothJointSector m n j := by
  refine ⟨Surface.uncurryE m u.val, ⟨?_, ?_⟩, ?_⟩
  · exact (domCcSmoothEquiv 3 m).symm u |>.property
  · change Surface.uncurryE m u.val ∈ Module.End.eigenspace
      (SurfaceSym.rotE m (SurfaceSym.rotUnit 3)) (KsIndex.FormIndex.zeta 3 ^ j)
    simpa only [SurfaceSym.rotUnit, Circle.coe_exp, Nat.cast_ofNat] using hr
  · apply Module.End.mem_eigenspace_iff.mpr
    funext p
    change u.val (p.1 + 2) p.2 = KsIndex.FormIndex.zeta m ^ n * u.val p.1 p.2
    rw [hp, paperRationalPhase_eq_zeta]

lemma paperSmoothJointOfFamily_chart (m n j : ℕ) [NeZero m]
    (u : Surface.CcSmooth 3 m) (hp) (hr) :
    (paperSmoothToChainSector m n j (paperSmoothJointOfFamily m n j u hp hr)).val.val =
      ccSmoothToChainChart 3 m u := by
  rfl

/-- Reconstructed paper slit characters have precisely the required chain character. -/
lemma paperSlit_reconstruct_character (m n j : ℕ) [NeZero m]
    (p : paperSlitCharacterDomain ((n : ℝ) / m) j) :
    chainChartRotationLI 3 m (-(2 * Real.pi) / 3) (paperRotation_root 3 (by decide))
      (reconstructChainPhase 3 m _ (paperRationalPhase_root m n) ⟨p.val, p.property.1⟩).val =
    KsIndex.FormIndex.zeta 3 ^ j •
      (reconstructChainPhase 3 m _ (paperRationalPhase_root m n) ⟨p.val, p.property.1⟩).val := by
  have h := (chainPhase_character_iff_pair 3 m _ _ (paperRotation_root 3 (by decide))
    (KsIndex.FormIndex.zeta 3 ^ j)
    (reconstructChainPhase 3 m _ (paperRationalPhase_root m n) ⟨p.val, p.property.1⟩)).mpr
    (by rw [chainPhasePair_reconstruct]; exact p.property.2)
  change chainChartRotationLI 3 m (-(2 * Real.pi) / 3) (paperRotation_root 3 (by decide))
    (reconstructChainPhase 3 m _ (paperRationalPhase_root m n) ⟨p.val, p.property.1⟩).val -
    KsIndex.FormIndex.zeta 3 ^ j •
    (reconstructChainPhase 3 m _ (paperRationalPhase_root m n) ⟨p.val, p.property.1⟩).val = 0 at h
  exact sub_eq_zero.mp h

/-- Original paper smooth joint-sector approximants for puncture-avoiding data. -/
theorem paperSlit_punctured_smooth_joint_approximation (m n j : ℕ) [NeZero m]
    (p : paperSlitCharacterDomain ((n : ℝ) / m) j) {ρ : ℝ} (hρ : 0 < ρ)
    (hu : ∀ᵐ z ∂volume.restrict disk,
      (∃ q ∈ Surface.punctures 3, ‖z - q‖ ≤ ρ) → valueCLM p.val.1 z = 0)
    (hv : ∀ᵐ z ∂volume.restrict disk,
      (∃ q ∈ Surface.punctures 3, ‖z - q‖ ≤ ρ) → valueCLM p.val.2 z = 0) :
    ∃ S : ℕ → paperSmoothJointSector m n j,
      Tendsto (fun i => (paperSmoothToChainSector m n j (S i)).val.val) atTop
        (𝓝 (reconstructChainPhase 3 m _ (paperRationalPhase_root m n)
          ⟨p.val, p.property.1⟩).val) := by
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
  obtain ⟨S, hp, hr, ht⟩ := punctured_slit_smooth_joint_approximation (by decide : 1 ≤ 3)
    _ (paperRationalPhase_root m n) ⟨p.val, p.property.1⟩ _
    (paperRotation_root 3 (by decide)) j (paperSlit_reconstruct_character m n j p)
    hH hpH (hzero hu) (hzero hv)
  exact ⟨fun i => paperSmoothJointOfFamily m n j (S i) (hp i) (hr i), ht⟩

lemma reconstructChainPhase_dist {k m : ℕ} [NeZero m] (c : ℂ) (hc : c ^ m = 1)
    (p q : slitTraceDomain k c) :
    dist (reconstructChainPhase k m c hc p).val (reconstructChainPhase k m c hc q).val =
      dist p.val q.val := by
  have h := (chainPhasePairLinearIsometryEquiv k m c hc).dist_map
    (reconstructChainPhase k m c hc p) (reconstructChainPhase k m c hc q)
  change dist (chainPhasePairLinearMap k m c (reconstructChainPhase k m c hc p))
    (chainPhasePairLinearMap k m c (reconstructChainPhase k m c hc q)) = _ at h
  rw [chainPhasePair_reconstruct, chainPhasePair_reconstruct] at h
  exact h.symm

/-- The genuine original smooth joint sector is dense in the weak joint sector.
No assertion about bounded Jacobi kernel representatives is used or implied. -/
theorem paperSmoothToChainSector_denseRange (m n j : ℕ) [NeZero m] :
    DenseRange (paperSmoothToChainSector m n j) := by
  rw [Metric.denseRange_iff]
  intro u ε hε
  let p : paperSlitCharacterDomain ((n : ℝ) / m) j :=
    ⟨(chainPhasePairLinearMap 3 m _ u.val).val,
      (chainPhasePairLinearMap 3 m _ u.val).property,
      (chainPhase_character_iff_pair 3 m _ _ (paperRotation_root 3 (by decide)) _
        u.val).mp u.property⟩
  obtain ⟨v, M, ρ, hM, hρ, hvp, hb1, hb2, hz1, hz2⟩ :=
    exists_paperSlit_puncture_approx _ j p (half_pos hε)
  obtain ⟨S, hS⟩ := paperSlit_punctured_smooth_joint_approximation m n j v hρ hz1 hz2
  obtain ⟨i, hi⟩ := (Metric.tendsto_nhds.mp hS (ε / 2) (half_pos hε)).exists
  let v' := reconstructChainPhase 3 m _ (paperRationalPhase_root m n) ⟨v.val, v.property.1⟩
  have hback : reconstructChainPhase 3 m _ (paperRationalPhase_root m n)
      ⟨p.val, p.property.1⟩ = u.val := reconstruct_chainPhasePair 3 m _ _ u.val
  have hdist : dist v'.val u.val.val < ε / 2 := by
    rw [← hback]
    rw [reconstructChainPhase_dist]
    simpa only [dist_eq_norm] using hvp
  refine ⟨S i, ?_⟩
  change dist u.val.val (paperSmoothToChainSector m n j (S i)).val.val < ε
  have htri := dist_triangle (paperSmoothToChainSector m n j (S i)).val.val v'.val u.val.val
  rw [dist_comm]
  exact lt_of_le_of_lt htri (by linarith)

end KsIndex.Spectral
