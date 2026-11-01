module

public import KsIndexLean.KarcherGlobalContinuity
public import Mathlib.Topology.OpenPartialHomeomorph.Constructions

@[expose] public section


/-! Explicit local Euclidean coordinates for the periodic ambient target.
Only the height coordinate is reduced modulo 2π. -/
noncomputable section
open Set Topology
open scoped ContDiff
namespace KsIndex.KarcherData

local instance : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩

/-- A quotient-projection chart on a vertical open strip of width 2π. -/
def periodProjectionChart (a : ℝ) : OpenPartialHomeomorph AmbientTriple PeriodTarget :=
  (OpenPartialHomeomorph.refl ℝ).prod
    ((OpenPartialHomeomorph.refl ℝ).prod (AddCircle.openPartialHomeomorphCoe (2 * Real.pi) a))

lemma periodProjectionChart_apply (a : ℝ) (p : AmbientTriple) :
    periodProjectionChart a p = projectPeriod p := rfl

lemma periodProjectionChart_source (a : ℝ) (p : AmbientTriple) :
    p ∈ (periodProjectionChart a).source ↔ a < p.2.2 ∧ p.2.2 < a + 2 * Real.pi := by
  simp [periodProjectionChart, OpenPartialHomeomorph.prod, AddCircle.openPartialHomeomorphCoe]

lemma periodProjectionChart_center_mem (p : AmbientTriple) :
    p ∈ (periodProjectionChart (p.2.2 - Real.pi)).source := by
  rw [periodProjectionChart_source]
  constructor <;> linarith [Real.pi_pos]

lemma periodProjectionChart_inverse {a : ℝ} {p : AmbientTriple}
    (hp : p ∈ (periodProjectionChart a).source) :
    (periodProjectionChart a).symm (projectPeriod p) = p :=
  (periodProjectionChart a).left_inv hp

lemma projectPeriod_surjective : Function.Surjective projectPeriod := by
  intro p
  obtain ⟨z, _, hz⟩ := AddCircle.eq_coe_Ico p.2.2
  exact ⟨(p.1, p.2.1, z), Prod.ext rfl (Prod.ext rfl hz)⟩

/-- Every ambient quotient point lies in one of these genuine local charts. -/
theorem periodProjectionChart_cover (p : PeriodTarget) :
    ∃ a : ℝ, p ∈ (periodProjectionChart a).target := by
  obtain ⟨q, rfl⟩ := projectPeriod_surjective p
  exact ⟨q.2.2 - Real.pi, (periodProjectionChart _).map_source (periodProjectionChart_center_mem q)⟩

/-- Near a given lift value, the inverse quotient chart recovers that real lift exactly. -/
theorem periodProjectionChart_local_lift {F : ℂ → AmbientTriple} {w : ℂ}
    (hF : ContinuousAt F w) :
    (fun z => (periodProjectionChart ((F w).2.2 - Real.pi)).symm (projectPeriod (F z))) =ᶠ[𝓝 w] F := by
  have he : ∀ᶠ z in 𝓝 w,
      F z ∈ (periodProjectionChart ((F w).2.2 - Real.pi)).source :=
    hF.preimage_mem_nhds ((periodProjectionChart _).open_source.mem_nhds
      (periodProjectionChart_center_mem (F w)))
  filter_upwards [he] with z hz
  exact periodProjectionChart_inverse hz

/-- A locally lifted quotient map has exactly the smoothness and real
 differential of its lift in these target coordinates. -/
theorem periodProjectionChart_smooth_lift {F : ℂ → AmbientTriple} {w : ℂ}
    (hF : ContDiffAt ℝ ∞ F w) :
    ContDiffAt ℝ ∞
      (fun z => (periodProjectionChart ((F w).2.2 - Real.pi)).symm (projectPeriod (F z))) w ∧
    fderiv ℝ (fun z => (periodProjectionChart ((F w).2.2 - Real.pi)).symm
      (projectPeriod (F z))) w = fderiv ℝ F w := by
  have he := periodProjectionChart_local_lift hF.continuousAt
  exact ⟨hF.congr_of_eventuallyEq he, he.fderiv_eq⟩

/-- Addition of a quotient constant introduces no change in the local real
 differential: choose a real lift of that constant and use a centered strip. -/
theorem quotient_constant_smooth_lift (C : PeriodTarget) {X : ℂ → AmbientTriple} {w : ℂ}
    (hX : ContDiffAt ℝ ∞ X w) :
    ∃ c : AmbientTriple, projectPeriod c = C ∧
      let a := (c + X w).2.2 - Real.pi
      (C + projectPeriod (X w)) ∈ (periodProjectionChart a).target ∧
      ContDiffAt ℝ ∞ (fun z => (periodProjectionChart a).symm (C + projectPeriod (X z))) w ∧
      fderiv ℝ (fun z => (periodProjectionChart a).symm (C + projectPeriod (X z))) w =
        fderiv ℝ X w := by
  obtain ⟨c, hc⟩ := projectPeriod_surjective C
  refine ⟨c, hc, ?_⟩
  dsimp only
  have hF : ContDiffAt ℝ ∞ (fun z => c + X z) w := contDiffAt_const.add hX
  have hs := periodProjectionChart_smooth_lift hF
  have ht : C + projectPeriod (X w) ∈ (periodProjectionChart ((c + X w).2.2 - Real.pi)).target := by
    rw [← hc, ← projectPeriod_add]
    exact (periodProjectionChart _).map_source (periodProjectionChart_center_mem _)
  refine ⟨ht, ?_, ?_⟩
  · simpa only [projectPeriod_add, hc] using hs.1
  · have hder : fderiv ℝ (fun z => c + X z) w = fderiv ℝ X w := by
      exact (hX.differentiableAt (by simp)).hasFDerivAt.const_add c |>.fderiv
    simpa only [projectPeriod_add, hc, hder] using hs.2

/-- An injective differential of the real lift remains injective in genuine
local coordinates of the periodic ambient quotient. -/
theorem quotient_constant_immersion_coordinates (C : PeriodTarget)
    {X : ℂ → AmbientTriple} {w : ℂ} (hX : ContDiffAt ℝ ∞ X w)
    (hinj : Function.Injective (fderiv ℝ X w)) :
    ∃ a : ℝ, C + projectPeriod (X w) ∈ (periodProjectionChart a).target ∧
      ContDiffAt ℝ ∞ (fun z => (periodProjectionChart a).symm (C + projectPeriod (X z))) w ∧
      Function.Injective (fderiv ℝ
        (fun z => (periodProjectionChart a).symm (C + projectPeriod (X z))) w) := by
  obtain ⟨c, _, ht, hs, hd⟩ := quotient_constant_smooth_lift C hX
  exact ⟨(c + X w).2.2 - Real.pi, ht, hs, hd ▸ hinj⟩

/-- Finite EW representatives are smooth immersions in actual quotient-target
coordinates, with no injectivity claim for the ambient image. -/
theorem ew_quotient_immersion_coordinates {k : ℕ} (hk : 2 ≤ k) (C : PeriodTarget)
    {X : ℂ → AmbientTriple} {w : ℂ} (hw : w ∉ Surface.punctures k)
    (hX : ContDiffAt ℝ ∞ X w) (hd : HasFDerivAt X (ewRealDifferential k w) w) :
    ∃ a : ℝ, C + projectPeriod (X w) ∈ (periodProjectionChart a).target ∧
      ContDiffAt ℝ ∞ (fun z => (periodProjectionChart a).symm (C + projectPeriod (X z))) w ∧
      Function.Injective (fderiv ℝ
        (fun z => (periodProjectionChart a).symm (C + projectPeriod (X z))) w) := by
  apply quotient_constant_immersion_coordinates C hX
  rw [hd.fderiv]
  exact ewRealDifferential_injective hk hw

/-- The same quotient-target statement holds at regular infinity. -/
theorem infinity_quotient_immersion_coordinates {k : ℕ} (hk : 2 ≤ k) (C : PeriodTarget)
    {X : ℂ → AmbientTriple} {w : ℂ} (hw : w ∉ Surface.punctures k)
    (hX : ContDiffAt ℝ ∞ X w) (hd : HasFDerivAt X (infinityRealDifferential k w) w) :
    ∃ a : ℝ, C + projectPeriod (X w) ∈ (periodProjectionChart a).target ∧
      ContDiffAt ℝ ∞ (fun z => (periodProjectionChart a).symm (C + projectPeriod (X z))) w ∧
      Function.Injective (fderiv ℝ
        (fun z => (periodProjectionChart a).symm (C + projectPeriod (X z))) w) := by
  apply quotient_constant_immersion_coordinates C hX
  rw [hd.fderiv]
  exact infinityRealDifferential_injective hk hw

/-- Changes of quotient coordinates are locally translations by a lattice
vector. This verifies the smooth compatibility of the target chart family. -/
theorem periodCoordinateChange_translation {a : ℝ} {q : AmbientTriple}
    (hq : projectPeriod q ∈ (periodProjectionChart a).target) :
    ∃ d : AmbientTriple, projectPeriod d = 0 ∧
      (fun z => (periodProjectionChart a).symm (projectPeriod z)) =ᶠ[𝓝 q] (fun z => z + d) := by
  let p := (periodProjectionChart a).symm (projectPeriod q)
  have hp : p ∈ (periodProjectionChart a).source := (periodProjectionChart a).map_target hq
  have he : projectPeriod p = projectPeriod q := (periodProjectionChart a).right_inv hq
  let d := p - q
  have hd : projectPeriod d = 0 := by rw [projectPeriod_sub, he, sub_self]
  refine ⟨d, hd, ?_⟩
  have hqd : q + d = p := by dsimp [d]; abel
  have hev : ∀ᶠ z in 𝓝 q, z + d ∈ (periodProjectionChart a).source := by
    apply (continuousAt_id.add continuousAt_const).preimage_mem_nhds
    change (periodProjectionChart a).source ∈ 𝓝 (q + d)
    rw [hqd]
    exact (periodProjectionChart a).open_source.mem_nhds hp
  filter_upwards [hev] with z hz
  have hz' : projectPeriod (z + d) = projectPeriod z := by rw [projectPeriod_add, hd, add_zero]
  rw [← hz']
  exact periodProjectionChart_inverse hz

/-- Target chart transitions are smooth with identity derivative; the local
Euclidean metric is unchanged by the vertical-period coordinate choices. -/
theorem periodCoordinateChange_smooth {a : ℝ} {q : AmbientTriple}
    (hq : projectPeriod q ∈ (periodProjectionChart a).target) :
    ContDiffAt ℝ ∞ (fun z => (periodProjectionChart a).symm (projectPeriod z)) q ∧
      HasFDerivAt (fun z => (periodProjectionChart a).symm (projectPeriod z))
        (ContinuousLinearMap.id ℝ AmbientTriple) q := by
  obtain ⟨d, _, he⟩ := periodCoordinateChange_translation hq
  exact ⟨(contDiffAt_id.add contDiffAt_const).congr_of_eventuallyEq he,
    ((hasFDerivAt_id q).add_const d).congr_of_eventuallyEq he⟩

end KsIndex.KarcherData
