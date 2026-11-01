module

public import KsIndexLean.KarcherGlobalImmersion

@[expose] public section


/-! Extension and basepoint-change tools for global EW equivariance. -/
noncomputable section
open Set Topology
open scoped Manifold
open scoped KsIndex.KarcherData.ParameterAtlas
namespace KsIndex.KarcherData

/-- Changing the basepoint changes only the additive constant. -/
theorem descendedIntegral_basepoint {k : ℕ} (hk : 2 ≤ k)
    (b c w : PuncturedPlane k) :
    descendedIntegral hk b w = descendedIntegral hk b c + descendedIntegral hk c w := by
  obtain ⟨D, hs, ht, hD⟩ := exists_connecting_chain hk c.property w.property
  rw [descendedIntegral_increment hk b c w D hs ht hD,
    descendedIntegral_eq hk c w D hs ht hD]

/-- Every singleton has dense complement in the actual parameter surface. -/
lemma parameter_dense_compl_singleton {k : ℕ} [Fact (2 ≤ k)] (p : ParameterSphere k) :
    Dense ({p}ᶜ : Set (ParameterSphere k)) := by
  apply dense_compl_singleton_iff_not_open.mpr
  intro ho
  have hc := (chartAt ℂ p).isOpen_image_of_subset_source ho
    (singleton_subset_iff.mpr (mem_chart_source ℂ p))
  rw [image_singleton] at hc
  exact not_isOpen_singleton (chartAt ℂ p p) hc

/-- Ordinary finite points are dense, so continuous identities extend to infinity. -/
theorem denseRange_finiteParameter {k : ℕ} [Fact (2 ≤ k)] :
    DenseRange (finiteParameter (k := k)) := by
  apply (parameter_dense_compl_singleton (infinityParameter k)).mono
  intro p hp
  rcases parameterSphere_cases p with hp' | hp'
  · exact (hp hp').elim
  · exact hp'

/-- Finite nonzero points are still dense; chart-swapping identities may therefore
be extended across both 0 and infinity. -/
theorem dense_finite_nonzero {k : ℕ} [Fact (2 ≤ k)] :
    Dense {p : ParameterSphere k | ∃ w : PuncturedPlane k, w.val ≠ 0 ∧ finiteParameter w = p} := by
  let : T2Space (ParameterSphere k) := inferInstanceAs
    (T2Space {p : Spherical.Sphere // p ∉ Spherical.sphereChart '' Surface.punctures k})
  let z : PuncturedPlane k := ⟨0, by
    simp [Surface.punctures, show 2 * k ≠ 0 by have := Fact.out (p := 2 ≤ k); omega]⟩
  have hd := (denseRange_finiteParameter (k := k)).inter_of_isOpen_right
    (parameter_dense_compl_singleton (finiteParameter z)) isOpen_compl_singleton
  apply hd.mono
  rintro p ⟨⟨w, rfl⟩, hw⟩
  refine ⟨w, ?_, rfl⟩
  intro h0
  apply hw
  congr 1
  exact Subtype.ext h0

/-- A continuous identity checked at finite nonzero points holds globally. -/
theorem parameter_eq_of_finite_nonzero {k : ℕ} [Fact (2 ≤ k)]
    {Y : Type*} [TopologicalSpace Y] [T2Space Y]
    {f g : ParameterSphere k → Y} (hf : Continuous f) (hg : Continuous g)
    (he : ∀ w : PuncturedPlane k, w.val ≠ 0 → f (finiteParameter w) = g (finiteParameter w)) :
    f = g := by
  apply funext
  intro p
  have hc : IsClosed {p | f p = g p} := isClosed_eq hf hg
  apply hc.closure_subset_iff.mpr ?_ (dense_finite_nonzero (k := k) p)
  rintro q ⟨w, hw, rfl⟩
  exact he w hw

/-- Global based maps differ by the same finite integral constant, including at infinity. -/
theorem extendedEWMap_basepoint {k : ℕ} [h : Fact (2 ≤ k)]
    (b c : PuncturedPlane k) (B C : PeriodTarget)
    (hb : Continuous (extendedEWMap h.out b B))
    (hc : Continuous (extendedEWMap h.out c C)) :
    extendedEWMap h.out b B =
      fun p => descendedIntegral h.out b c + extendedEWMap h.out c C p := by
  apply parameter_eq_of_finite_nonzero hb
    (show Continuous (fun p => descendedIntegral h.out b c + extendedEWMap h.out c C p)
      from continuous_const.add hc)
  intro w _
  simp only [extendedEWMap_finite]
  exact descendedIntegral_basepoint h.out b c w

/-- Generic global affine equivariance: only the ordinary-point identity and
continuity are needed to fill in the two regular chart centers. -/
theorem extendedEWMap_affine_equivariance {k : ℕ} [h : Fact (2 ≤ k)]
    (b : PuncturedPlane k) (C D : PeriodTarget)
    (τ : ParameterSphere k → ParameterSphere k) (A : PeriodTarget → PeriodTarget)
    (hF : Continuous (extendedEWMap h.out b C)) (hτ : Continuous τ) (hA : Continuous A)
    (he : ∀ w : PuncturedPlane k, w.val ≠ 0 →
      extendedEWMap h.out b C (τ (finiteParameter w)) = D + A (descendedIntegral h.out b w)) :
    ∀ p, extendedEWMap h.out b C (τ p) = D + A (extendedEWMap h.out b C p) := by
  have heq := parameter_eq_of_finite_nonzero (hF.comp hτ)
    (show Continuous (fun p => D + A (extendedEWMap h.out b C p))
      from continuous_const.add (hA.comp hF))
    (fun w hw => by simpa only [Function.comp_apply, extendedEWMap_finite] using he w hw)
  exact congrFun heq

/-- Convert a two-basepoint finite equivariance identity into the exact affine
identity for one fixed global map. The displacement is evaluated, not discarded. -/
theorem extendedEWMap_of_based_equivariance {k : ℕ} [h : Fact (2 ≤ k)]
    (b : PuncturedPlane k) (hb0 : b.val ≠ 0) (C : PeriodTarget)
    (t : {w : PuncturedPlane k // w.val ≠ 0} → PuncturedPlane k)
    (τ : ParameterSphere k → ParameterSphere k) (A : PeriodTarget → PeriodTarget)
    (hF : Continuous (extendedEWMap h.out b C)) (hτ : Continuous τ) (hA : Continuous A)
    (ht : ∀ w : {w : PuncturedPlane k // w.val ≠ 0},
      τ (finiteParameter w.val) = finiteParameter (t w))
    (he : ∀ w : {w : PuncturedPlane k // w.val ≠ 0},
      descendedIntegral h.out (t ⟨b, hb0⟩) (t w) = A (descendedIntegral h.out b w.val)) :
    ∀ p, extendedEWMap h.out b C (τ p) =
      descendedIntegral h.out b (t ⟨b, hb0⟩) + A (extendedEWMap h.out b C p) := by
  apply extendedEWMap_affine_equivariance b C _ τ A hF hτ hA
  intro w hw
  rw [ht ⟨w, hw⟩, extendedEWMap_finite,
    descendedIntegral_basepoint h.out b (t ⟨b, hb0⟩) (t ⟨w, hw⟩), he ⟨w, hw⟩]

end KsIndex.KarcherData
