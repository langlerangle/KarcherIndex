module

public import KsIndexLean.KarcherConnectingPaths
public import Mathlib.Topology.Instances.AddCircle.Defs

@[expose] public section


/-! The quotient-valued integral map on the finite punctured plane.
Only the third (vertical) coordinate is reduced modulo the literal period 2π.
This constructs no covering, immersion, or identification with the disk/seam model.
The basepoint law fixes the additive origin only, not the surface's positional normalization.
No continuity, chart at infinity, or geometric identification is claimed. -/
noncomputable section
namespace KsIndex.KarcherData
open Piecewise

/-- The finite punctured chart, without an identification with the seam model. -/
def PuncturedPlane (k : ℕ) := {w : ℂ // w ∉ Surface.punctures k}

/-- The algebraic period target; only the third coordinate is a quotient. -/
abbrev PeriodTarget := ℝ × ℝ × AddCircle (2 * Real.pi)

/-- Preserve horizontal displacements and reduce vertical displacement modulo 2π. -/
def projectPeriod (p : ℝ × ℝ × ℝ) : PeriodTarget :=
  (p.1, p.2.1, (p.2.2 : AddCircle (2 * Real.pi)))

lemma projectPeriod_zero : projectPeriod 0 = 0 := by
  simp [projectPeriod]

lemma projectPeriod_add (p q : ℝ × ℝ × ℝ) :
    projectPeriod (p + q) = projectPeriod p + projectPeriod q := by
  simp [projectPeriod]

/-- Convert the actual vertical lattice, with its explicit integer scalar convention. -/
lemma projectPeriod_eq_of_sub_lattice {p q : ℝ × ℝ × ℝ} {n : ℤ}
    (h : p - q = (0, 0, (2 * Real.pi) * (n : ℝ))) :
    projectPeriod p = projectPeriod q := by
  have h1 := congrArg Prod.fst h
  have h2 := congrArg (fun v : ℝ × ℝ × ℝ => v.2.1) h
  have h3 := congrArg (fun v : ℝ × ℝ × ℝ => v.2.2) h
  change p.1 - q.1 = 0 at h1
  change p.2.1 - q.2.1 = 0 at h2
  change p.2.2 - q.2.2 = (2 * Real.pi) * (n : ℝ) at h3
  have hv : ((p.2.2 - q.2.2 : ℝ) : AddCircle (2 * Real.pi)) = 0 := by
    apply (AddCircle.coe_eq_zero_iff (2 * Real.pi)).mpr
    refine ⟨n, ?_⟩
    rw [h3, zsmul_eq_mul, mul_comm]
  have he : (p.2.2 : AddCircle (2 * Real.pi)) = q.2.2 := by
    apply sub_eq_zero.mp
    simpa only [AddCircle.coe_sub] using hv
  exact Prod.ext (sub_eq_zero.mp h1) (Prod.ext (sub_eq_zero.mp h2) he)

/-- The quotient projection of the actual chain integral. -/
def quotientIntegral (k : ℕ) (C : Chain) : PeriodTarget :=
  projectPeriod (periodVector k C)

/-- Actual common endpoints and puncture avoidance imply equality of quotient integrals. -/
theorem quotientIntegral_congr {k : ℕ} (hk : 2 ≤ k) (C D : Chain)
    (hs : C.start = D.start) (ht : C.finish = D.finish)
    (hC : ∀ z ∈ Surface.punctures k, C.Avoids z)
    (hD : ∀ z ∈ Surface.punctures k, D.Avoids z) :
    quotientIntegral k C = quotientIntegral k D := by
  obtain ⟨n, hn⟩ := path_difference_mem_lattice hk C D hs ht hC hD
  exact projectPeriod_eq_of_sub_lattice hn

private def selectedChain {k : ℕ} (hk : 2 ≤ k) (b w : PuncturedPlane k) : Chain :=
  Classical.choose (exists_connecting_chain hk b.property w.property)

private lemma selectedChain_spec {k : ℕ} (hk : 2 ≤ k) (b w : PuncturedPlane k) :
    (selectedChain hk b w).start = b.val ∧ (selectedChain hk b w).finish = w.val ∧
      ∀ z ∈ Surface.punctures k, (selectedChain hk b w).Avoids z :=
  Classical.choose_spec (exists_connecting_chain hk b.property w.property)

/-- The based quotient-valued integral; the public characterization is witness-independent. -/
def descendedIntegral {k : ℕ} (hk : 2 ≤ k) (b w : PuncturedPlane k) : PeriodTarget :=
  quotientIntegral k (Classical.choose (exists_connecting_chain hk b.property w.property))

/-- Any actual avoiding chain with the specified endpoints computes the map. -/
theorem descendedIntegral_eq {k : ℕ} (hk : 2 ≤ k) (b w : PuncturedPlane k)
    (C : Chain) (hs : C.start = b.val) (ht : C.finish = w.val)
    (hC : ∀ z ∈ Surface.punctures k, C.Avoids z) :
    descendedIntegral hk b w = quotientIntegral k C := by
  obtain ⟨hb, hw, hA⟩ := selectedChain_spec hk b w
  exact quotientIntegral_congr hk _ C (hb.trans hs.symm) (hw.trans ht.symm) hA hC

/-- The basepoint has zero displacement. This fixes only the additive origin. -/
theorem descendedIntegral_self {k : ℕ} (hk : 2 ≤ k) (b : PuncturedPlane k) :
    descendedIntegral hk b b = 0 := by
  have hA : ∀ z ∈ Surface.punctures k, (Chain.identity b.val).Avoids z := by
    intro z hz
    apply Chain.identity_avoids
    intro he
    exact b.property (he.symm ▸ hz)
  rw [descendedIntegral_eq hk b b (Chain.identity b.val) rfl rfl hA,
    quotientIntegral, periodVector_identity, projectPeriod_zero]

/-- Increment along any actual avoiding chain, derived from concatenation of integrals. -/
theorem descendedIntegral_increment {k : ℕ} (hk : 2 ≤ k)
    (b x y : PuncturedPlane k) (D : Chain)
    (hs : D.start = x.val) (ht : D.finish = y.val)
    (hD : ∀ z ∈ Surface.punctures k, D.Avoids z) :
    descendedIntegral hk b y = descendedIntegral hk b x + quotientIntegral k D := by
  obtain ⟨C, hCs, hCt, hC⟩ := exists_connecting_chain hk b.property x.property
  let hjoin : C.finish = D.start := hCt.trans hs.symm
  have hA : ∀ z ∈ Surface.punctures k, (C.append D hjoin).Avoids z :=
    fun z hz => C.append_avoids D hjoin (hC z hz) (hD z hz)
  rw [descendedIntegral_eq hk b y (C.append D hjoin)
    ((Chain.append_start C D hjoin).trans hCs)
    ((Chain.append_finish C D hjoin).trans ht) hA,
    descendedIntegral_eq hk b x C hCs hCt hC]
  exact congrArg projectPeriod (periodVector_append hk C D hjoin hC hD) |>.trans
    (projectPeriod_add _ _)

end KsIndex.KarcherData
