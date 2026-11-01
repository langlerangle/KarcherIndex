module

public import Mathlib.Analysis.Complex.Polynomial.Basic

@[expose] public section


/-! A concrete waypoint off finitely many lines, found on a real parabola. -/
noncomputable section
namespace KsIndex.Piecewise
open Polynomial

def parabolaPoint (t : ℝ) : ℂ := (t : ℂ) + Complex.I * (t : ℂ) ^ 2

def obstaclePoly (a z : ℂ) : Polynomial ℝ :=
  C (z - a).re * X ^ 2 - C (z - a).im * X +
    C ((z - a).im * a.re - (z - a).re * a.im)

lemma obstaclePoly_ne_zero {a z : ℂ} (h : z ≠ a) : obstaclePoly a z ≠ 0 := by
  intro hp
  have h2 := congrArg (fun p : Polynomial ℝ => p.coeff 2) hp
  have h1 := congrArg (fun p : Polynomial ℝ => p.coeff 1) hp
  norm_num [obstaclePoly, sub_mul] at h2 h1
  apply h
  apply Complex.ext
  · linarith
  · linarith

lemma obstaclePoly_eval (a z : ℂ) (t : ℝ) :
    (obstaclePoly a z).eval t =
      (z - a).re * ((parabolaPoint t).im - a.im) -
        (z - a).im * ((parabolaPoint t).re - a.re) := by
  simp [obstaclePoly, parabolaPoint, Complex.mul_re, Complex.mul_im, pow_two]
  ring

lemma obstaclePoly_eq_zero_of_line {a z : ℂ} {t s : ℝ}
    (h : z = a + (s : ℂ) * (parabolaPoint t - a)) :
    (obstaclePoly a z).eval t = 0 := by
  rw [obstaclePoly_eval, h]
  simp [Complex.mul_re, Complex.mul_im]
  ring

/-- A waypoint for both endpoints avoiding every obstacle line. No bounded-region claim. -/
theorem exists_finite_obstacle_waypoint (S : Finset ℂ) (x y : ℂ)
    (hx : x ∉ S) (hy : y ∉ S) :
    ∃ c : ℂ, (∀ z ∈ S, ∀ s : ℝ, z ≠ x + (s : ℂ) * (c - x)) ∧
      (∀ z ∈ S, ∀ s : ℝ, z ≠ y + (s : ℂ) * (c - y)) := by
  classical
  let bad (a : ℂ) : Finset ℝ := S.biUnion (fun z => (obstaclePoly a z).roots.toFinset)
  obtain ⟨t, ht⟩ := Infinite.exists_notMem_finset (bad x ∪ bad y)
  have good (a : ℂ) (ha : a ∉ S) (ht : t ∉ bad a) :
      ∀ z ∈ S, ∀ s : ℝ, z ≠ a + (s : ℂ) * (parabolaPoint t - a) := by
    intro z hz s he
    have hza : z ≠ a := by intro h; exact ha (h ▸ hz)
    apply ht
    apply Finset.mem_biUnion.mpr
    refine ⟨z, hz, ?_⟩
    apply Multiset.mem_toFinset.mpr
    apply (Polynomial.mem_roots (obstaclePoly_ne_zero hza)).mpr
    exact obstaclePoly_eq_zero_of_line he
  exact ⟨parabolaPoint t, good x hx (fun h => ht (Finset.mem_union_left _ h)),
    good y hy (fun h => ht (Finset.mem_union_right _ h))⟩

end KsIndex.Piecewise
