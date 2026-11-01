module

public import KsIndexLean.KarcherGlobalFirstGeometry
public import Mathlib.Topology.Connected.TotallyDisconnected

@[expose] public section


/-! Pointwise uniqueness up to sign of the actual oriented unit normal. -/
noncomputable section
namespace KsIndex.KarcherData

lemma euclideanSq_eq_zero {a : AmbientTriple} (ha : euclideanSq a = 0) : a = 0 := by
  unfold euclideanSq at ha
  have h1 : a.1 = 0 := by nlinarith [sq_nonneg a.2.1, sq_nonneg a.2.2]
  have h2 : a.2.1 = 0 := by nlinarith [sq_nonneg a.1, sq_nonneg a.2.2]
  have h3 : a.2.2 = 0 := by nlinarith [sq_nonneg a.1, sq_nonneg a.2.1]
  exact Prod.ext h1 (Prod.ext h2 h3)

lemma euclideanCross_cross (a b c : AmbientTriple) :
    euclideanCross (euclideanCross a b) c =
      euclideanDot a c • b - euclideanDot b c • a := by
  apply Prod.ext
  · simp only [euclideanCross, euclideanDot, Prod.smul_fst, Prod.fst_sub, smul_eq_mul]
    ring
  · apply Prod.ext <;>
      simp only [euclideanCross, euclideanDot, Prod.smul_fst, Prod.smul_snd,
        Prod.fst_sub, Prod.snd_sub, smul_eq_mul] <;> ring

lemma euclideanCross_smul_left (r : ℝ) (a b : AmbientTriple) :
    euclideanCross (r • a) b = r • euclideanCross a b := by
  apply Prod.ext
  · simp only [euclideanCross, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]; ring
  · apply Prod.ext <;>
      simp only [euclideanCross, Prod.smul_fst, Prod.smul_snd, smul_eq_mul] <;> ring

lemma unit_parallel_eq_or_neg {a b : AmbientTriple}
    (ha : euclideanSq a = 1) (hb : euclideanSq b = 1)
    (hc : euclideanCross a b = 0) : a = b ∨ a = -b := by
  have hd := euclideanCross_sq a b
  rw [hc, ha, hb] at hd
  have hs : euclideanDot a b ^ 2 = 1 := by
    simp only [euclideanSq, Prod.fst_zero, Prod.snd_zero, zero_pow (by decide : 2 ≠ 0),
      zero_add, one_mul] at hd
    linarith
  rcases sq_eq_one_iff.mp hs with hp | hn
  · left
    apply sub_eq_zero.mp
    apply euclideanSq_eq_zero
    have he : euclideanSq (a - b) = euclideanSq a + euclideanSq b - 2 * euclideanDot a b := by
      simp only [euclideanSq, euclideanDot, Prod.fst_sub, Prod.snd_sub]; ring
    rw [he, ha, hb, hp]
    norm_num
  · right
    apply eq_neg_of_add_eq_zero_left
    apply euclideanSq_eq_zero
    have he : euclideanSq (a + b) = euclideanSq a + euclideanSq b + 2 * euclideanDot a b := by
      simp only [euclideanSq, euclideanDot, Prod.fst_add, Prod.snd_add]; ring
    rw [he, ha, hb, hn]
    norm_num

/-- Any unit vector orthogonal to both actual coordinate tangents is one of
the two orientations of their unit normal. -/
theorem chart_unit_normal_eq_or_neg {X : ℂ → AmbientTriple} {w : ℂ} {N : AmbientTriple}
    (hN : euclideanSq N = 1) (hchart : euclideanSq (chartUnitNormal X w) = 1)
    (hu : euclideanDot (fderiv ℝ X w 1) N = 0)
    (hv : euclideanDot (fderiv ℝ X w Complex.I) N = 0) :
    N = chartUnitNormal X w ∨ N = -chartUnitNormal X w := by
  have hc : euclideanCross (chartUnitNormal X w) N = 0 := by
    rw [chartUnitNormal, euclideanCross_smul_left, euclideanCross_cross, hu, hv]
    simp only [zero_smul, sub_self, smul_zero]
  rcases unit_parallel_eq_or_neg hchart hN hc with he | he
  · exact Or.inl he.symm
  · exact Or.inr (by rw [he, neg_neg])

lemma euclideanDot_self (a : AmbientTriple) : euclideanDot a a = euclideanSq a := by
  simp only [euclideanDot, euclideanSq, pow_two]

lemma euclideanDot_neg_left (a b : AmbientTriple) :
    euclideanDot (-a) b = -euclideanDot a b := by
  simp only [euclideanDot, Prod.fst_neg, Prod.snd_neg]
  ring

/-- Continuous unit fields which agree up to sign on a connected space have
their orientation fixed by agreement at a single point. -/
theorem continuous_unit_field_eq_of_eq_at {P : Type*} [TopologicalSpace P]
    [PreconnectedSpace P] {N M : P → AmbientTriple}
    (hN : Continuous N) (hM : Continuous M) (hunit : ∀ p, euclideanSq (M p) = 1)
    (hsign : ∀ p, N p = M p ∨ N p = -M p)
    (p₀ : P) (h₀ : N p₀ = M p₀) : N = M := by
  let f : P → ℝ := fun p => euclideanDot (N p) (M p)
  have hf : Continuous f := by
    dsimp [f, euclideanDot]
    fun_prop
  have hs (p : P) : f p ∈ ({1, -1} : Set ℝ) := by
    rcases hsign p with hp | hp
    · simp only [f, hp, euclideanDot_self, hunit, Set.mem_insert_iff, Set.mem_singleton_iff]
      exact Or.inl trivial
    · simp only [f, hp, euclideanDot_neg_left, euclideanDot_self, hunit,
        Set.mem_insert_iff, Set.mem_singleton_iff]
      exact Or.inr trivial
  have hconstant (p : P) : f p = f p₀ :=
    isPreconnected_univ.constant_of_mapsTo (Set.toFinite ({1, -1} : Set ℝ)).isDiscrete
      hf.continuousOn (fun x _ => hs x) (Set.mem_univ p) (Set.mem_univ p₀)
  have hbase : f p₀ = 1 := by simp only [f, h₀, euclideanDot_self, hunit]
  funext p
  rcases hsign p with hp | hp
  · exact hp
  · have hh := (hconstant p).trans hbase
    simp only [f, hp, euclideanDot_neg_left, euclideanDot_self, hunit] at hh
    norm_num at hh

namespace PaperHalfPeriodRealization
open scoped KsIndex.KarcherData.ParameterAtlas KsIndex.KarcherData.PeriodicAmbient
variable {k : ℕ} [h : Fact (2 ≤ k)]

/-- On this actual connected immersion, a competing continuous unit normal
is fixed everywhere by its orientation at one point. -/
theorem normal_unique_of_eq_at (R : PaperHalfPeriodRealization k)
    (N : PeriodicEWCarrier h.out (reflectionBasepoint k) R.C → AmbientTriple)
    (hN : Continuous N) (hunit : ∀ q, euclideanSq (N q) = 1)
    (hu : ∀ q, euclideanDot
      (fderiv ℝ (R.centeredChart q) (R.chartCenter q) 1) (N q) = 0)
    (hv : ∀ q, euclideanDot
      (fderiv ℝ (R.centeredChart q) (R.chartCenter q) Complex.I) (N q) = 0)
    (q₀ : PeriodicEWCarrier h.out (reflectionBasepoint k) R.C)
    (h₀ : N q₀ = R.normal q₀) : N = R.normal := by
  let := R.connected
  apply continuous_unit_field_eq_of_eq_at hN R.continuous_normal R.normal_unit _ q₀ h₀
  intro q
  have hc : euclideanSq (chartUnitNormal (R.centeredChart q) (R.chartCenter q)) = 1 := by
    rw [← R.normal_eq_centeredChart q]
    exact R.normal_unit q
  have hs := chart_unit_normal_eq_or_neg (hunit q) hc (hu q) (hv q)
  rwa [← R.normal_eq_centeredChart q] at hs

end PaperHalfPeriodRealization

end KsIndex.KarcherData
