module

public import KsIndexLean.EnergySmoothBound
public import KsIndexLean.PunctureCutoffP

@[expose] public section


/-!
# From local end bounds to bounded fields

A continuous function on an open set inherits a pointwise bound from a
continuous bounded representative with the same almost-everywhere values.

For an `EnergySmooth` family, bounds near each puncture combine with the
compact-part bound to give `IsBounded`. Each assumed end bound is uniform
over all copies and all points in its neighborhood. Finiteness of the
puncture set gives a common positive radius and a common end bound.
Inserting `1` before taking the minimum radius and `0` before taking the
maximum bound also handles an empty puncture set.
-/

noncomputable section
open Set MeasureTheory
namespace KsIndex.FaithfulInjection
open KsIndex.Surface KsIndex.PunctureCutoff

/-! ### Transfer of a representative bound -/

/-- A function continuous on an open set, a.e.-equal there to a function
with a continuous globally bounded representative, satisfies the bound
pointwise on the open set. -/
lemma norm_le_of_ae_eq_continuousOn {U : Set ℂ} (hU : IsOpen U)
    {F g h : ℂ → ℂ} (hF : ContinuousOn F U) (hg : Continuous g)
    {M : ℝ} (hM : ∀ z, ‖g z‖ ≤ M)
    (hFh : F =ᵐ[volume.restrict U] h) (hgh : g =ᵐ[volume.restrict U] h) :
    ∀ z ∈ U, ‖F z‖ ≤ M := by
  have hFg : F =ᵐ[volume.restrict U] g := hFh.trans hgh.symm
  have heq : Set.EqOn F g U :=
    MeasureTheory.Measure.eqOn_open_of_ae_eq hFg hU hF hg.continuousOn
  intro z hz
  rw [heq hz]
  exact hM z

/-! ### Assembly of local and compact-part bounds -/

/-- An `EnergySmooth` family with a bound near every puncture is bounded.
The finite set of radii, together with `1`, has a positive minimum.
The compact-part bound covers points outside these neighborhoods, and
finitely many end constants give a uniform bound inside them. The end
hypothesis includes all copies and the puncture points themselves. -/
theorem isBounded_of_end_bounds {k m : ℕ} [NeZero m] (hk : 1 ≤ k)
    {u : ZMod (2 * m) → ℂ → ℂ} (hu : u ∈ EnergySmooth k m)
    (hend : ∀ p ∈ punctures k, ∃ δ : ℝ, 0 < δ ∧ ∃ C : ℝ, ∀ n, ∀ w : ℂ,
      ‖w - p‖ < δ → ‖u n w‖ ≤ C) :
    IsBounded u := by
  classical
  choose! δf hδf Cf hCf using hend
  -- the uniform radius: the minimum of the per-puncture radii and 1
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
  -- the compact-part constant
  obtain ⟨C0, hC0⟩ := energySmooth_bounded_away hu hεpos
  -- the uniform end constant
  set T : Finset ℝ := insert (0 : ℝ) ((pF k).image Cf) with hTdef
  have hTne : T.Nonempty := Finset.insert_nonempty _ _
  set Cend : ℝ := T.max' hTne with hCenddef
  have hCle : ∀ p ∈ punctures k, Cf p ≤ Cend := by
    intro p hp
    apply T.le_max'
    rw [hTdef]
    exact Finset.mem_insert_of_mem
      (Finset.mem_image_of_mem Cf ((mem_pF hk).mpr hp))
  -- assemble
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

end KsIndex.FaithfulInjection
