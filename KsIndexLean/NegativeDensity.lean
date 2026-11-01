module

/-
Dense linear pullback preserves finite negative dimensions. The analytic density
and form-identification hypotheses are inputs, not consequences of this module.
-/
public import KsIndexLean.NegativeApproximation
public import Mathlib

@[expose] public section


noncomputable section
open scoped ENNReal
open Complex Finset

namespace KsIndex.NegativeDensity

/-- Continuous Hermitian form, with the paper's conjugate-first convention. -/
structure Sesq {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (B : E → E → ℂ) : Prop where
  addL : ∀ a b v, B (a + b) v = B a v + B b v
  addR : ∀ a v w, B a (v + w) = B a v + B a w
  smulL : ∀ c a v, B (c • a) v = (starRingEnd ℂ) c * B a v
  smulR : ∀ c a v, B a (c • v) = c * B a v
  conj : ∀ u v, B v u = (starRingEnd ℂ) (B u v)
  continuous : Continuous (fun p : E × E => B p.1 p.2)

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
variable {B : E → E → ℂ}

lemma Sesq.zeroL (h : Sesq B) (v : E) : B 0 v = 0 := by
  simpa using h.smulL 0 (0 : E) v

lemma Sesq.zeroR (h : Sesq B) (v : E) : B v 0 = 0 := by
  simpa using h.smulR 0 v (0 : E)

lemma Sesq.sumL (h : Sesq B) {α : Type*} (s : Finset α) (f : α → E) (v : E) :
    B (∑ a ∈ s, f a) v = ∑ a ∈ s, B (f a) v := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [h.zeroL]
  | @insert a s ha ih => simp [Finset.sum_insert, ha, h.addL, ih]

lemma Sesq.sumR (h : Sesq B) {α : Type*} (s : Finset α) (f : α → E) (v : E) :
    B v (∑ a ∈ s, f a) = ∑ a ∈ s, B v (f a) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [h.zeroR]
  | @insert a s ha ih => simp [Finset.sum_insert, ha, h.addR, ih]

lemma Sesq.gram (h : Sesq B) {d : ℕ} (v : Fin d → E) (c : Fin d → ℂ) :
    (B (∑ a, c a • v a) (∑ a, c a • v a)).re =
      NegativeApproximation.quadratic (fun a b => B (v a) (v b)) c := by
  unfold NegativeApproximation.quadratic
  congr 1
  rw [h.sumL]
  apply Finset.sum_congr rfl
  intro a _
  rw [h.sumR]
  apply Finset.sum_congr rfl
  intro b _
  rw [h.smulL, h.smulR]
  ring

/-- Approximate an entire negative frame, retaining every negative direction. -/
theorem exists_negative_frame_approx
    {S : Type*} [AddCommGroup S] [Module ℂ S]
    (hB : Sesq B) (i : S →ₗ[ℂ] E) (hi : DenseRange i)
    {d : ℕ} (v : Fin d → E)
    (hv : ∀ c : Fin d → ℂ, c ≠ 0 →
      (B (∑ j, c j • v j) (∑ j, c j • v j)).re < 0)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ s : Fin d → S, (∀ j, ‖i (s j) - v j‖ < ε) ∧
      ∀ c : Fin d → ℂ, c ≠ 0 →
        (B (i (∑ j, c j • s j)) (i (∑ j, c j • s j))).re < 0 := by
  classical
  by_cases hd : d = 0
  · subst d
    refine ⟨fun j => Fin.elim0 j, ?_, ?_⟩
    · intro j; exact Fin.elim0 j
    · intro c hc
      exact (hc (Subsingleton.elim _ _)).elim
  have hdpos : 1 ≤ d := Nat.one_le_iff_ne_zero.mpr hd
  let A : Matrix (Fin d) (Fin d) ℂ := fun a b => B (v a) (v b)
  obtain ⟨δ, hδ, hmargin⟩ := NegativeApproximation.exists_uniform_negative_margin A
    (fun c hc => by
      change NegativeApproximation.quadratic (fun a b => B (v a) (v b)) c < 0
      rw [← hB.gram]
      exact hv c hc)
  let t : ℝ := δ / (2 * (d : ℝ))
  have ht : 0 < t := by dsimp [t]; positivity
  let U : Set (Fin d → E) := {w | (∀ j, ‖w j - v j‖ < ε) ∧
    ∀ a b, ‖B (w a) (w b) - A a b‖ < t}
  have hU : IsOpen U := by
    dsimp [U]
    simp only [Set.ofPred_and, Set.ofPred_forall]
    apply IsOpen.inter
    · apply isOpen_iInter_of_finite
      intro j
      have hc : Continuous (fun w : Fin d → E => ‖w j - v j‖) :=
        ((continuous_apply j).sub continuous_const).norm
      exact isOpen_lt hc continuous_const
    · apply isOpen_iInter_of_finite
      intro a
      apply isOpen_iInter_of_finite
      intro b
      have hp : Continuous (fun w : Fin d → E => (w a, w b)) := by fun_prop
      have hb : Continuous (fun w : Fin d → E => B (w a) (w b)) :=
        hB.continuous.comp hp
      have hc : Continuous (fun w : Fin d → E => ‖B (w a) (w b) - A a b‖) :=
        (hb.sub continuous_const).norm
      exact isOpen_lt hc continuous_const
  have hvU : v ∈ U := by
    exact ⟨fun j => by simpa using hε, fun a b => by simpa [A] using ht⟩
  have hdense : DenseRange (fun s : Fin d → S => fun j => i (s j)) :=
    DenseRange.piMap (fun _ => hi)
  obtain ⟨s, hs⟩ := hdense.exists_mem_open hU ⟨v, hvU⟩
  refine ⟨s, hs.1, ?_⟩
  intro c hc
  have he : 0 < NegativeApproximation.energy c := by
    unfold NegativeApproximation.energy
    obtain ⟨j, hj⟩ : ∃ j, c j ≠ 0 := by
      by_contra hh
      push Not at hh
      exact hc (funext hh)
    exact Finset.sum_pos' (fun _ _ => sq_nonneg _) ⟨j, Finset.mem_univ _, sq_pos_of_ne_zero
      (norm_ne_zero_iff.mpr hj)⟩
  have hm := NegativeApproximation.negative_margin_of_entrywise_close hdpos hδ hmargin
    (fun a b => (hs.2 a b).le) c
  have hn : NegativeApproximation.quadratic (fun a b => B (i (s a)) (i (s b))) c < 0 :=
    lt_of_le_of_lt hm (mul_neg_of_neg_of_pos (neg_lt_zero.mpr (half_pos hδ)) he)
  simpa only [map_sum, map_smul, hB.gram] using hn

/-- The full variational index, on any complex vector space. -/
def negativeIndex {X : Type*} [AddCommGroup X] [Module ℂ X] (Q : X → ℝ) : ℕ∞ :=
  ⨆ (V : Submodule ℂ X) (_ : ∀ x ∈ V, x ≠ 0 → Q x < 0)
    (_ : FiniteDimensional ℂ V), (Module.finrank ℂ V : ℕ∞)

/-- A negative coefficient form forces independence of the underlying frame. -/
lemma linearIndependent_of_negative_frame (hB : Sesq B) {d : ℕ} (v : Fin d → E)
    (hv : ∀ c : Fin d → ℂ, c ≠ 0 →
      (B (∑ j, c j • v j) (∑ j, c j • v j)).re < 0) :
    LinearIndependent ℂ v := by
  rw [Fintype.linearIndependent_iff]
  intro c hc j
  by_contra hj
  have hcn : c ≠ 0 := fun h => hj (congrFun h j)
  have h := hv c hcn
  rw [hc, hB.zeroL] at h
  simp at h

/-- Independence upstairs does not require global injectivity of the dense map. -/
lemma independent_negative_image_frame
    {S : Type*} [AddCommGroup S] [Module ℂ S]
    (hB : Sesq B) (i : S →ₗ[ℂ] E) {d : ℕ} (s : Fin d → S)
    (hs : ∀ c : Fin d → ℂ, c ≠ 0 →
      (B (i (∑ j, c j • s j)) (i (∑ j, c j • s j))).re < 0) :
    LinearIndependent ℂ s ∧ LinearIndependent ℂ (fun j => i (s j)) := by
  have h : LinearIndependent ℂ (fun j => i (s j)) :=
    linearIndependent_of_negative_frame hB _ (by simpa only [map_sum, map_smul] using hs)
  exact ⟨LinearIndependent.of_comp i h, h⟩

/-- A negative frame spans exactly its number of independent negative directions. -/
lemma negative_frame_span (hB : Sesq B) {d : ℕ} (v : Fin d → E)
    (hv : ∀ c : Fin d → ℂ, c ≠ 0 →
      (B (∑ j, c j • v j) (∑ j, c j • v j)).re < 0) :
    (∀ x ∈ Submodule.span ℂ (Set.range v), x ≠ 0 → (B x x).re < 0) ∧
      Module.finrank ℂ (Submodule.span ℂ (Set.range v)) = d := by
  constructor
  · intro x hx hn
    rw [← Fintype.range_linearCombination] at hx
    obtain ⟨c, rfl⟩ := hx
    have hc : c ≠ 0 := fun h => hn (by simp [h])
    simpa only [Fintype.linearCombination_apply] using hv c hc
  · simpa using finrank_span_eq_card (linearIndependent_of_negative_frame hB v hv)

/-- The source span also has the prescribed negative dimension, even with a kernel. -/
lemma negative_image_frame_source_span
    {S : Type*} [AddCommGroup S] [Module ℂ S]
    (hB : Sesq B) (i : S →ₗ[ℂ] E) {d : ℕ} (s : Fin d → S)
    (hs : ∀ c : Fin d → ℂ, c ≠ 0 →
      (B (i (∑ j, c j • s j)) (i (∑ j, c j • s j))).re < 0) :
    (∀ x ∈ Submodule.span ℂ (Set.range s), x ≠ 0 → (B (i x) (i x)).re < 0) ∧
      Module.finrank ℂ (Submodule.span ℂ (Set.range s)) = d := by
  constructor
  · intro x hx hn
    rw [← Fintype.range_linearCombination] at hx
    obtain ⟨c, rfl⟩ := hx
    have hc : c ≠ 0 := fun h => hn (by simp [h])
    simpa only [Fintype.linearCombination_apply] using hs c hc
  · simpa using finrank_span_eq_card (independent_negative_image_frame hB i s hs).1

/-- A form-preserving map is injective on a negative subspace. -/
lemma injective_on_negative {X Y : Type*}
    [AddCommGroup X] [Module ℂ X] [AddCommGroup Y] [Module ℂ Y]
    (Q : Y → ℝ) (hQ : Q 0 = 0) (f : X →ₗ[ℂ] Y)
    (hneg : ∀ x : X, x ≠ 0 → Q (f x) < 0) : Function.Injective f := by
  apply LinearMap.ker_eq_bot.mp
  apply bot_unique
  intro x hx
  rw [Submodule.mem_bot]
  by_contra h
  have hn := hneg x h
  rw [LinearMap.mem_ker.mp hx, hQ] at hn
  exact (lt_irrefl 0 hn)

/-- Pullback cannot increase index; a kernel contributes no negative direction. -/
theorem negativeIndex_pullback_le {X Y : Type*}
    [AddCommGroup X] [Module ℂ X] [AddCommGroup Y] [Module ℂ Y]
    (Q : Y → ℝ) (hQ : Q 0 = 0) (f : X →ₗ[ℂ] Y) :
    negativeIndex (fun x => Q (f x)) ≤ negativeIndex Q := by
  classical
  unfold negativeIndex
  refine iSup_le fun V => iSup_le fun hV => iSup_le fun hfin => ?_
  let := hfin
  let g : V →ₗ[ℂ] Y := f.comp V.subtype
  have hinj : Function.Injective g := injective_on_negative Q hQ g (by
    intro x hx
    exact hV x x.property (fun h => hx (Subtype.ext h)))
  have hneg : ∀ y ∈ LinearMap.range g, y ≠ 0 → Q y < 0 := by
    rintro y ⟨x, rfl⟩ hy
    exact hV x x.property (fun h => hy (by simp [g, h]))
  have hdim := LinearMap.finrank_range_of_inj hinj
  rw [← hdim]
  exact le_iSup_of_le (LinearMap.range g) (le_iSup_of_le hneg
    (le_iSup_of_le (inferInstance : FiniteDimensional ℂ (LinearMap.range g)) le_rfl))

/-- A dense linear map transfers every finite negative dimension. -/
theorem negativeIndex_le_pullback
    {S : Type*} [AddCommGroup S] [Module ℂ S]
    (hB : Sesq B) (i : S →ₗ[ℂ] E) (hi : DenseRange i) :
    negativeIndex (fun x => (B x x).re) ≤
      negativeIndex (fun s => (B (i s) (i s)).re) := by
  classical
  unfold negativeIndex
  refine iSup_le fun V => iSup_le fun hV => iSup_le fun hfin => ?_
  let := hfin
  let d := Module.finrank ℂ V
  let b := Module.finBasis ℂ V
  let v : Fin d → E := fun j => (b j : E)
  have hv : ∀ c : Fin d → ℂ, c ≠ 0 →
      (B (∑ j, c j • v j) (∑ j, c j • v j)).re < 0 := by
    intro c hc
    have hn : (∑ j, c j • b j : V) ≠ 0 := by
      intro hz
      have hz' := (Fintype.linearIndependent_iff.mp b.linearIndependent) c hz
      exact hc (funext hz')
    have hcoe : (∑ j, c j • v j) = ((∑ j, c j • b j : V) : E) := by
      simp [v]
    rw [hcoe]
    exact hV _ (∑ j, c j • b j : V).property (fun h => hn (Subtype.ext h))
  obtain ⟨s, _, hs⟩ := exists_negative_frame_approx hB i hi v hv (show (0 : ℝ) < 1 by norm_num)
  let g : (Fin d → ℂ) →ₗ[ℂ] S := Fintype.linearCombination ℂ s
  have hneg : ∀ c, c ≠ 0 → (B (i (g c)) (i (g c))).re < 0 := by
    simpa [g, Fintype.linearCombination_apply] using hs
  have hzero : (B (i (0 : S)) (i 0)).re = 0 := by simp [hB.zeroL]
  have hinj : Function.Injective g := injective_on_negative
    (fun s => (B (i s) (i s)).re) hzero g hneg
  have hr : ∀ x ∈ LinearMap.range g, x ≠ 0 → (B (i x) (i x)).re < 0 := by
    rintro x ⟨c, rfl⟩ hx
    exact hneg c (fun hc => hx (by simp [hc]))
  have hdim : Module.finrank ℂ (LinearMap.range g) = Module.finrank ℂ V := by
    rw [LinearMap.finrank_range_of_inj hinj]
    simp [d]
  rw [← hdim]
  exact le_iSup_of_le (LinearMap.range g) (le_iSup_of_le hr
    (le_iSup_of_le (inferInstance : FiniteDimensional ℂ (LinearMap.range g)) le_rfl))

/-- Dense form pullback preserves the full index, including infinity. -/
theorem negativeIndex_pullback_of_denseRange
    {S : Type*} [AddCommGroup S] [Module ℂ S]
    (hB : Sesq B) (i : S →ₗ[ℂ] E) (hi : DenseRange i) :
    negativeIndex (fun s => (B (i s) (i s)).re) =
      negativeIndex (fun x => (B x x).re) := by
  apply le_antisymm
  · exact negativeIndex_pullback_le (fun x => (B x x).re) (by simp [hB.zeroL]) i
  · exact negativeIndex_le_pullback hB i hi

end KsIndex.NegativeDensity
