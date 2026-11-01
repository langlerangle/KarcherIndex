module

public import KsIndexLean.KarcherHalfPeriodClassical
public import KsIndexLean.KarcherDiskSupport

@[expose] public section


/-! Compact support on the actual closed half-period is equivalent to
uniform vanishing near its deleted ends in the disk coordinate. No
smoothness or differential boundary condition is used. -/
noncomputable section
open Set Topology
open scoped KsIndex.KarcherData.ParameterAtlas KsIndex.KarcherData.PeriodicAmbient
namespace KsIndex.KarcherData.PaperHalfPeriodRealization
variable {k : ℕ} [h : Fact (2 ≤ k)]

lemma halfPeriod_hasCompactSupport_iff (R : PaperHalfPeriodRealization k)
    (f : PaperHalfPeriod h.out (reflectionBasepoint k) R.C → ℂ) :
    HasCompactSupport f ↔ SingleDisk.SuppAwayP1 k (R.halfPeriodCoordinate f) := by
  let V : PaperHalfPeriod h.out (reflectionBasepoint k) R.C → ℂ :=
    fun q => (R.diskHomeomorph q).val.val
  have hemb : IsEmbedding (fun w : PuncturedClosedDisk k => w.val.val) :=
    IsEmbedding.subtypeVal.comp IsEmbedding.subtypeVal
  have hV : Continuous V := hemb.continuous.comp R.diskHomeomorph.continuous
  constructor
  · intro hf
    have hc := hf.image hV
    have hp : IsClosed (Surface.punctures k) :=
      isClosed_eq (continuous_id.pow (2 * k)) continuous_const
    have hd : Disjoint (V '' tsupport f) (Surface.punctures k) := by
      apply Set.disjoint_left.mpr
      rintro z ⟨q, hq, rfl⟩ hz
      exact (R.diskHomeomorph q).val.property hz
    obtain ⟨ε, hε, he⟩ := Metric.exists_pos_forall_lt_edist hc hp hd
    refine ⟨ε, hε, fun z hz => ?_⟩
    classical
    unfold halfPeriodCoordinate
    split_ifs with hzD
    · by_contra hn
      let w : PuncturedClosedDisk k := ⟨⟨z,hzD.2⟩,hzD.1⟩
      have ht : R.diskHomeomorph.symm w ∈ tsupport f := subset_tsupport f hn
      obtain ⟨p, hp, hzp⟩ := hz
      have hh := he _ ⟨_, ht, rfl⟩ p hp
      have hv : V (R.diskHomeomorph.symm w) = z := by
        exact congrArg (fun a : PuncturedClosedDisk k => a.val.val)
          (R.diskHomeomorph.apply_symm_apply w)
      rw [hv] at hh
      have hdist : ε < ‖z - p‖ := by
        simpa only [edist_nndist, ENNReal.coe_lt_coe, ← NNReal.coe_lt_coe,
          coe_nndist, dist_eq_norm] using hh
      exact (not_lt_of_ge hdist.le) hzp
    · rfl
  · rintro ⟨ε,hε,hf⟩
    have hc : IsCompact (R.diskHomeomorph ⁻¹' diskCore k ε) := by
      have he : R.diskHomeomorph ⁻¹' diskCore k ε =
          R.diskHomeomorph.symm '' diskCore k ε := by
        ext q
        constructor
        · intro hq
          exact ⟨R.diskHomeomorph q, hq, R.diskHomeomorph.symm_apply_apply q⟩
        · rintro ⟨w, hw, rfl⟩
          change R.diskHomeomorph (R.diskHomeomorph.symm w) ∈ diskCore k ε
          rwa [R.diskHomeomorph.apply_symm_apply]
      rw [he]
      exact (diskCore_isCompact hε).image R.diskHomeomorph.symm.continuous
    apply HasCompactSupport.intro' hc
      ((diskCore_isClosed ε).preimage R.diskHomeomorph.continuous)
    intro q hq
    change ¬ ∀ p ∈ Surface.punctures k, ε ≤ ‖V q - p‖ at hq
    push Not at hq
    have hz := hf (V q) hq
    have he := R.halfPeriodCoordinate_apply f (R.diskHomeomorph q)
    simpa only [Homeomorph.symm_apply_apply] using he.symm.trans hz

end KsIndex.KarcherData.PaperHalfPeriodRealization
