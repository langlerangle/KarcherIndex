module

public import KsIndexLean.GeneralConstrainedApproximation
public import KsIndexLean.JoinedDiskFields
public import KsIndexLean.AristotleJoinedPunctureHole
public import KsIndexLean.JacobiFamily

@[expose] public section


/-!
# Puncture-neighborhood vanishing for joined disk values

A disk-side puncture-vanishing hypothesis is transported to almost-everywhere
vanishing on a whole-plane neighborhood of each puncture. This supplies the
puncture hypothesis used by the reflected boundary-mollifier constructions.
For `k ≥ 1` and a positive disk-side radius, each puncture has a positive
whole-plane radius; the conclusion does not assert a common radius for all punctures.
The complex joining coefficient is arbitrary. The proof applies
`AstraAristotle.joined_puncture_hole` after identifying its joined value with
`joinedDiskValue`.
-/

open Set MeasureTheory Filter Topology
noncomputable section
namespace KsIndex.Trace
open KsIndex.WeakH1

/-- `AstraAristotle.joined (valueCLM v) c` is definitionally `joinedDiskValue v v c`
(`inversion ≡ radialInversion`, `radialJoin 1`). -/
lemma joined_valueCLM_eq (v : ComplexH1) (c : ℂ) :
    AstraAristotle.joined (fun z => valueCLM v z) c = joinedDiskValue v v c := by
  funext z
  simp only [AstraAristotle.joined, joinedDiskValue, radialJoin, AstraAristotle.inversion,
    radialInversion]

/-- From disk-side puncture-neighborhood vanishing for `v` and any complex coefficient `c`, the joined
value `joinedDiskValue v v c` has a whole-plane AE hole around every puncture — exactly the `hP`
hypothesis of the reflected boundary-mollifier cores (before ρ-localization). -/
lemma joinedDiskValue_puncture_hP {k : ℕ} (hk : 1 ≤ k) {v : ComplexH1} {ρ : ℝ} (hρ : 0 < ρ)
    (hvz : ∀ᵐ z ∂volume.restrict (disk : Set ℂ),
      (∃ p ∈ Surface.punctures k, ‖z - p‖ ≤ ρ) → valueCLM v z = 0)
    (c : ℂ) :
    ∀ p ∈ Surface.punctures k, ∃ R : ℝ, 0 < R ∧
      ∀ᵐ w ∂(volume : Measure ℂ), dist w p < R → joinedDiskValue v v c w = 0 := by
  intro p hp
  have hpn : ‖p‖ = 1 := KsIndex.JacobiFamily.punctures_norm_eq_one hk hp
  have hf : ∀ᵐ z ∂volume.restrict (Metric.ball (0 : ℂ) 1),
      dist z p < ρ → (fun z => valueCLM v z) z = 0 := by
    have hdisk : (disk : Set ℂ) = Metric.ball (0 : ℂ) 1 := rfl
    rw [← hdisk]
    filter_upwards [hvz] with z hz hzp
    refine hz ⟨p, hp, ?_⟩
    rw [dist_eq_norm] at hzp
    exact hzp.le
  obtain ⟨r, hr, hr0⟩ :=
    AstraAristotle.joined_puncture_hole (fun z => valueCLM v z) c p hpn hρ hf
  refine ⟨r, hr, ?_⟩
  filter_upwards [hr0] with w hw hwp
  rw [← joined_valueCLM_eq v c]
  exact hw hwp

end KsIndex.Trace
