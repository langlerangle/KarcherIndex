module

public import KsIndexLean.IndexCoordinateTransport

@[expose] public section


noncomputable section
namespace KsIndex.Spectral
open KsIndex.NegativeDensity

variable {E F : Type*} [AddCommGroup E] [Module ℂ E] [AddCommGroup F] [Module ℂ F]

/-- Independent negative spaces combine without losing either component's
dimension. The forms are allowed to be degenerate outside those spaces. -/
lemma negative_product_dimension (Q : E → ℝ) (R : F → ℝ)
    (hQ : Q 0 = 0) (hR : R 0 = 0)
    (U : Submodule ℂ E) (V : Submodule ℂ F)
    [FiniteDimensional ℂ U] [FiniteDimensional ℂ V]
    (hU : ∀ x ∈ U, x ≠ 0 → Q x < 0)
    (hV : ∀ y ∈ V, y ≠ 0 → R y < 0) :
    (Module.finrank ℂ U + Module.finrank ℂ V : ℕ∞) ≤
      negativeIndex (fun z : E × F => Q z.1 + R z.2) := by
  let T : (U × V) →ₗ[ℂ] E × F := U.subtype.prodMap V.subtype
  have hT : Function.Injective T := by
    intro x y h
    apply Prod.ext
    · exact Subtype.ext (congrArg Prod.fst h)
    · exact Subtype.ext (congrArg Prod.snd h)
  have hn : ∀ z ∈ LinearMap.range T, z ≠ 0 → Q z.1 + R z.2 < 0 := by
    rintro z ⟨w, rfl⟩ hw
    have hq : Q w.1.val ≤ 0 := by
      by_cases h : w.1.val = 0
      · rw [h, hQ]
      · exact (hU _ w.1.property h).le
    have hr : R w.2.val ≤ 0 := by
      by_cases h : w.2.val = 0
      · rw [h, hR]
      · exact (hV _ w.2.property h).le
    change Q w.1.val + R w.2.val < 0
    by_cases ha : w.1.val = 0
    · have hb : w.2.val ≠ 0 := by
        intro hb
        apply hw
        exact Prod.ext ha hb
      have hh := hV _ w.2.property hb
      linarith
    · have hh := hU _ w.1.property ha
      linarith
  have hd : Module.finrank ℂ (LinearMap.range T) = Module.finrank ℂ U + Module.finrank ℂ V :=
    (LinearMap.finrank_range_of_inj hT).trans Module.finrank_prod
  have hh : (Module.finrank ℂ (LinearMap.range T) : ℕ∞) ≤
      negativeIndex (fun z : E × F => Q z.1 + R z.2) :=
    le_iSup_of_le (LinearMap.range T) (le_iSup_of_le hn
      (le_iSup_of_le (inferInstance : FiniteDimensional ℂ (LinearMap.range T)) le_rfl))
  simpa only [hd, Nat.cast_add] using hh


lemma negativeIndex_biSup (Q : E → ℝ) :
    negativeIndex Q = ⨆ (U : Submodule ℂ E)
      (_ : (∀ x ∈ U, x ≠ 0 → Q x < 0) ∧ FiniteDimensional ℂ U),
        (Module.finrank ℂ U : ℕ∞) := by
  simp only [negativeIndex, iSup_and]

/-- The full lower half of orthogonal-product index additivity, including
infinite variational indices. -/
lemma negativeIndex_add_le_product (Q : E → ℝ) (R : F → ℝ)
    (hQ : Q 0 = 0) (hR : R 0 = 0) :
    negativeIndex Q + negativeIndex R ≤ negativeIndex (fun z : E × F => Q z.1 + R z.2) := by
  rw [negativeIndex_biSup Q, negativeIndex_biSup R]
  apply ENat.biSup_add_biSup_le'
    ⟨⊥, ⟨fun x hx hn => hn ((Submodule.mem_bot ℂ).mp hx) |>.elim, inferInstance⟩⟩
    ⟨⊥, ⟨fun x hx hn => hn ((Submodule.mem_bot ℂ).mp hx) |>.elim, inferInstance⟩⟩
  rintro U ⟨hU, hfdU⟩ V ⟨hV, hfdV⟩
  let := hfdU
  let := hfdV
  exact negative_product_dimension Q R hQ hR U V hU hV


/-- Nonnegative kernel coordinates bound the dimension of every negative
subspace. No complement decomposition or spectral enumeration is assumed. -/
lemma negativeIndex_le_of_nonnegative_kernel
    {K : Type*} [AddCommGroup K] [Module ℂ K] [FiniteDimensional ℂ K]
    (Q : E → ℝ) (T : E →ₗ[ℂ] K) (hT : ∀ u, T u = 0 → 0 ≤ Q u) :
    negativeIndex Q ≤ (Module.finrank ℂ K : ℕ∞) := by
  unfold negativeIndex
  refine iSup_le fun W => iSup_le fun hW => iSup_le fun hfd => ?_
  let := hfd
  let g := T.comp W.subtype
  have hz (u : W) (hu : g u = 0) : u = 0 := by
    by_contra hn
    have hneg := hW u.val u.property (fun h => hn (Subtype.ext h))
    have hpos := hT u.val hu
    linarith
  have hinj : Function.Injective g := by
    intro u v huv
    apply sub_eq_zero.mp
    apply hz
    rw [map_sub, huv, sub_self]
  have hd := LinearMap.finrank_le_finrank_of_injective hinj
  exact_mod_cast hd

lemma negativeIndex_product_upper
    {K L : Type*} [AddCommGroup K] [Module ℂ K] [FiniteDimensional ℂ K]
    [AddCommGroup L] [Module ℂ L] [FiniteDimensional ℂ L]
    (Q : E → ℝ) (R : F → ℝ) (T : E →ₗ[ℂ] K) (S : F →ₗ[ℂ] L)
    (hT : ∀ u, T u = 0 → 0 ≤ Q u) (hS : ∀ v, S v = 0 → 0 ≤ R v) :
    negativeIndex (fun z : E × F => Q z.1 + R z.2) ≤
      (Module.finrank ℂ K + Module.finrank ℂ L : ℕ∞) := by
  have h := negativeIndex_le_of_nonnegative_kernel
    (fun z : E × F => Q z.1 + R z.2) (T.prodMap S) (by
      intro z hz
      exact add_nonneg (hT z.1 (congrArg Prod.fst hz)) (hS z.2 (congrArg Prod.snd hz)))
  simpa only [Module.finrank_prod, Nat.cast_add] using h

/-- Equality follows when the nonnegative-kernel coordinate dimensions equal
the component indices. Spectral consumers must supply those exact dimensions. -/
lemma negativeIndex_product_eq_of_coordinates
    {K L : Type*} [AddCommGroup K] [Module ℂ K] [FiniteDimensional ℂ K]
    [AddCommGroup L] [Module ℂ L] [FiniteDimensional ℂ L]
    (Q : E → ℝ) (R : F → ℝ) (hQ : Q 0 = 0) (hR : R 0 = 0)
    (T : E →ₗ[ℂ] K) (S : F →ₗ[ℂ] L)
    (hT : ∀ u, T u = 0 → 0 ≤ Q u) (hS : ∀ v, S v = 0 → 0 ≤ R v)
    (hK : negativeIndex Q = (Module.finrank ℂ K : ℕ∞))
    (hL : negativeIndex R = (Module.finrank ℂ L : ℕ∞)) :
    negativeIndex (fun z : E × F => Q z.1 + R z.2) = negativeIndex Q + negativeIndex R := by
  apply le_antisymm
  · rw [hK, hL]
    exact negativeIndex_product_upper Q R T S hT hS
  · exact negativeIndex_add_le_product Q R hQ hR

end KsIndex.Spectral
