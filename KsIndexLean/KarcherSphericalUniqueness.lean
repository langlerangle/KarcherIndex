module

public import KsIndexLean.KarcherCoverOrientation
public import KsIndexLean.KarcherCoverRatio

@[expose] public section


/-! Uniqueness on the full punctured parameter sphere, including infinity. -/
noncomputable section
open Set
namespace KsIndex.KarcherData

/-- A continuous spherical map preserving the oriented Gauss field and the
labeled upper arc at 1 is the identity. Finite-coordinate extraction and
agreement at infinity are conclusions of the proof. -/
theorem normal_preserving_parameter_map_unique {k : ℕ} (hk : 2 ≤ k)
    (g : ParameterSphere k → ParameterSphere k) (hg : Continuous g)
    (hN : ∀ p, parameterNormal (g p) = parameterNormal p)
    (hone : (1 : ℂ) ∉ Surface.punctures k)
    (harc : ∃ v : PuncturedPlane k,
      g (finiteParameter ⟨1, hone⟩) = finiteParameter v ∧ v.val ∈ Surface.arc k 1) :
    g = id := by
  classical
  let : Fact (2 ≤ k) := ⟨hk⟩
  let : T2Space (ParameterSphere k) := inferInstanceAs
    (T2Space {p : Spherical.Sphere // p ∉ Spherical.sphereChart '' Surface.punctures k})
  have hex (w : PuncturedPlane k) : ∃ v : PuncturedPlane k,
      finiteParameter v = g (finiteParameter w) := by
    rcases parameterSphere_cases (g (finiteParameter w)) with hp | hp
    · have hh := hN (finiteParameter w)
      rw [hp, parameterNormal_infinity] at hh
      exact (parameterNormal_finite_ne_north w hh.symm).elim
    · exact hp
  let Q : PuncturedPlane k → PuncturedPlane k := fun w => Classical.choose (hex w)
  have hQ (w : PuncturedPlane k) : finiteParameter (Q w) = g (finiteParameter w) :=
    Classical.choose_spec (hex w)
  have hQc : Continuous Q := by
    apply (isOpenEmbedding_finiteParameter k).isEmbedding.continuous_iff.mpr
    have he : finiteParameter ∘ Q = g ∘ finiteParameter := funext hQ
    rw [he]
    exact hg.comp (continuous_finiteParameter k)
  let f : ℂ → ℂ := fun w => if hw : w ∉ Surface.punctures k then (Q ⟨w, hw⟩).val else 0
  have hfval (w : PuncturedPlane k) : f w.val = (Q w).val := by
    simp only [f, dite_eq_left w.property]
    exact congrArg (fun p : PuncturedPlane k => (Q p).val) (Subtype.ext rfl)
  have hfc : ContinuousOn f {w | w ∉ Surface.punctures k} := by
    apply continuousOn_iff_continuous_domRestrict.mpr
    have he : ({w | w ∉ Surface.punctures k}.domRestrict f) =
        (fun w : PuncturedPlane k => (Q w).val) := funext hfval
    rw [he]
    exact continuous_subtype_val.comp hQc
  have hpow (w : ℂ) (hw : w ∉ Surface.punctures k) : f w ^ (k - 1) = w ^ (k - 1) := by
    let x : PuncturedPlane k := ⟨w, hw⟩
    have hh : stereoNormal (gauss k (Q x).val) = stereoNormal (gauss k x.val) :=
      (parameterNormal_finite (Q x)).symm.trans
        ((congrArg parameterNormal (hQ x)).trans
          ((hN (finiteParameter x)).trans (parameterNormal_finite x)))
    have he := congrArg (fun a => Spherical.stereoCoord (tripleToEuclidean a)) hh
    simp only [stereoCoord_stereoNormal] at he
    rw [hfval ⟨w, hw⟩]
    exact he
  have havoid (w : ℂ) (hw : w ∉ Surface.punctures k) : f w ∉ Surface.punctures k := by
    rw [hfval ⟨w, hw⟩]
    exact (Q ⟨w, hw⟩).property
  have hfa : f 1 ∈ Surface.arc k 1 := by
    obtain ⟨v, hv, hva⟩ := harc
    have he : Q ⟨1, hone⟩ = v :=
      (finiteParameter_injective k) ((hQ ⟨1, hone⟩).trans hv)
    rw [hfval ⟨1, hone⟩, he]
    exact hva
  have hid := finite_coordinate_unique hk hfc hpow havoid hfa
  apply (denseRange_finiteParameter (k := k)).equalizer hg continuous_id
  funext w
  change g (finiteParameter w) = finiteParameter w
  rw [← hQ]
  apply congrArg finiteParameter
  apply Subtype.ext
  rw [← hfval]
  exact hid w.val w.property

end KsIndex.KarcherData
