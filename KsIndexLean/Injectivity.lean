module

/-
Almost-everywhere injectivity of bounded smooth Jacobi fields.

`boundedJacobi_ae_ext` shows that two members of `BoundedJacobi` agreeing
almost everywhere on each open disk are equal as representatives. This
strengthens the pointwise-on-`chainDom` encoding result `boundedJacobi_ext`.

The proof first upgrades almost-everywhere agreement to pointwise agreement
on the open disk by continuity. One-sided smoothness, through the closed-disk
germ `exists_germ_closedBall`, extends agreement to the seam arcs. At punctures,
`PunctureZero` supplies equality by normalization, rather than by a limit.
The result then follows from `boundedJacobi_ext`.
-/
public import KsIndexLean.Caccioppoli

@[expose] public section


open Complex Real MeasureTheory Filter Topology
open scoped ContDiff

noncomputable section

namespace KsIndex.FaithfulInjection

open KsIndex.Surface KsIndex.SurfaceForm KsIndex.SeamNormal

variable {k m : ℕ} {u v : ZMod (2 * m) → ℂ → ℂ}

/-! ### Step (i): a.e.-agreement ⟹ pointwise on the open disk (interior continuity) -/

/-- **Step (i).**  On the open disk `u n` and `v n` are continuous (interior smoothness), so
a.e.-agreement there upgrades to pointwise agreement: the set where they differ is open (continuity)
and null (a.e.), hence empty (`volume` is an open-positive measure on `ℂ`). -/
lemma eqOn_disk_of_ae (hu : IsSmooth k m u) (hv : IsSmooth k m v) (n : ZMod (2 * m))
    (h : u n =ᵐ[volume.restrict disk] v n) : Set.EqOn (u n) (v n) disk := by
  intro w₀ hw₀
  by_contra hne
  set D : Set ℂ := disk ∩ {w | u n w ≠ v n w} with hD
  have hDopen : IsOpen D := by
    rw [isOpen_iff_mem_nhds]
    rintro z ⟨hzdisk, hzne⟩
    have hcu : ContinuousAt (u n) z := (differentiableAt_of_isSmooth hu n hzdisk).continuousAt
    have hcv : ContinuousAt (v n) z := (differentiableAt_of_isSmooth hv n hzdisk).continuousAt
    have hg : ContinuousAt (fun w => u n w - v n w) z := hcu.sub hcv
    have hev : ∀ᶠ w in 𝓝 z, (fun w => u n w - v n w) w ≠ 0 :=
      hg.eventually_ne (sub_ne_zero.mpr hzne)
    have hne_nbhd : {w | u n w ≠ v n w} ∈ 𝓝 z := by
      filter_upwards [hev] with w hw using sub_ne_zero.mp hw
    exact Filter.inter_mem (Metric.isOpen_ball.mem_nhds hzdisk) hne_nbhd
  have hDne : D.Nonempty := ⟨w₀, hw₀, hne⟩
  have hnull : (volume.restrict disk) {w | u n w ≠ v n w} = 0 := by
    have := ae_iff.mp h
    simpa using this
  have hDnull : volume D = 0 := by
    rw [hD, Set.inter_comm, ← Measure.restrict_apply' measurableSet_disk]
    exact hnull
  have hDpos : 0 < volume D := hDopen.measure_pos volume hDne
  rw [hDnull] at hDpos
  exact lt_irrefl 0 hDpos

/-! ### Step (ii): open-disk agreement ⟹ agreement on the seam arcs (one-sided continuity) -/

/-- **Step (ii).**  At a seam-arc point `w₀` (on the circle, off the punctures), `u n` and `v n`
each equal a `C^∞`-at-`w₀` germ on the whole closed disk near `w₀` (`exists_germ_closedBall`, using
`SeamVal`).  The two germs agree on the open disk near `w₀` (step (i)); since `w₀` lies in the
closure of the open disk and both germs are continuous there, the germs agree AT `w₀` — so
`u n w₀ = v n w₀`.  This is the step beyond bare continuity: the boundary VALUE, not just the
interior trace. -/
lemma eq_of_seam_of_eqOn_disk (hu : IsSmooth k m u) (hsvu : SeamVal k u)
    (hv : IsSmooth k m v) (hsvv : SeamVal k v) (n : ZMod (2 * m))
    (heq : Set.EqOn (u n) (v n) disk) {w₀ : ℂ} (hw₀ : ‖w₀‖ = 1) (hp : w₀ ∉ punctures k) :
    u n w₀ = v n w₀ := by
  obtain ⟨Fu, hFuc, Wu, hWuopen, hwWu, hWueq⟩ := exists_germ_closedBall hu hsvu n hw₀ hp
  obtain ⟨Fv, hFvc, Wv, hWvopen, hwWv, hWveq⟩ := exists_germ_closedBall hv hsvv n hw₀ hp
  rw [hWueq w₀ hwWu (le_of_eq hw₀), hWveq w₀ hwWv (le_of_eq hw₀)]
  have hbot : (𝓝[disk] w₀).NeBot := by
    rw [← mem_closure_iff_nhdsWithin_neBot, disk, closure_ball (0 : ℂ) one_ne_zero,
      Metric.mem_closedBall, dist_zero_right]
    exact le_of_eq hw₀
  have hFueq : Fu =ᶠ[𝓝[disk] w₀] Fv := by
    filter_upwards [nhdsWithin_le_nhds (hWuopen.mem_nhds hwWu),
      nhdsWithin_le_nhds (hWvopen.mem_nhds hwWv), self_mem_nhdsWithin] with z hzWu hzWv hzdisk
    have hz1 : ‖z‖ ≤ 1 := le_of_lt (mem_disk_iff.mp hzdisk)
    rw [← hWueq z hzWu hz1, ← hWveq z hzWv hz1]
    exact heq hzdisk
  exact tendsto_nhds_unique hFuc.continuousAt.continuousWithinAt
    (hFvc.continuousAt.continuousWithinAt.congr' hFueq.symm)

/-! ### The a.e.-injectivity theorem (steps (i)–(iv) assembled) -/

/-- **O3 — a.e.-injectivity (faithfulness).**  Two bounded smooth Jacobi fields agreeing a.e. (per
copy, on the open disk) are EQUAL as representatives.  The geometric field is determined by its
a.e.-class: the faithful injection `BoundedJacobi ↪ WeakKer` loses no information in the passage to
the a.e./`L²` world.  Steps: (i) `eqOn_disk_of_ae` (open disk), (ii) `eq_of_seam_of_eqOn_disk` (seam
arcs), (iii) punctures + (iv) exterior via `boundedJacobi_ext`. -/
theorem boundedJacobi_ae_ext (hu : u ∈ BoundedJacobi k m) (hv : v ∈ BoundedJacobi k m)
    (h : ∀ n, u n =ᵐ[volume.restrict disk] v n) : u = v := by
  refine boundedJacobi_ext hu hv (fun n w hw => ?_)
  obtain ⟨hw1, hwp⟩ := hw
  have hdiskeq : Set.EqOn (u n) (v n) disk := eqOn_disk_of_ae hu.1 hv.1 n (h n)
  by_cases hlt : ‖w‖ < 1
  · exact hdiskeq (mem_disk_iff.mpr hlt)
  · exact eq_of_seam_of_eqOn_disk hu.1 hu.2.2.2.2 hv.1 hv.2.2.2.2 n hdiskeq
      (le_antisymm hw1 (not_lt.mp hlt)) hwp

end KsIndex.FaithfulInjection
