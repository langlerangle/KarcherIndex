module

/-
Index and nullity are additive over a finite orthogonal decomposition.

`Sesq Q B D` supplies a Hermitian form with diagonal `Q`, additive in both
slots and complex-linear in the second slot on `D`. `OrthDecomp B D Dblk`
supplies finitely many pairwise orthogonal subdomains and linear projections:
each projection lands in its block, their sum is the identity on `D`, and each
vanishes on the other blocks. These are algebraic hypotheses; no topology,
completeness, or group action is required.

The conclusions `formIndex_eq_sum` and `formNullity_eq_sum` are equalities in
`ℕ∞`, so infinite index or nullity is allowed. For index superadditivity,
finite-dimensional negative block subspaces assemble through the injective
sum map. For the reverse inequality, when all block indices are finite, a
maximal negative subspace in each block has a nonnegative orthogonal
complement. Pairing projected vectors against bases of those negative
subspaces gives an injective map on any negative subspace of `D`.

For nullity, block radicals assemble into the domain radical, and the block
projections send domain-radical vectors into block radicals. The resulting
injective maps give both dimension inequalities. Applications to character
decompositions must separately construct the projections and prove their
orthogonality and reconstruction properties.
-/
public import KsIndexLean.FormIndex

@[expose] public section


noncomputable section

namespace KsIndex.FormIndex

open Classical Module

variable {ι : Type*}

/-! ### The sesquilinear structure of `B` on the domain -/

/-- The sesquilinear structure the additivity theorems consume: `B` is Hermitian, additive in both
slots on `D`, and `ℂ`-linear in the second slot on `D`. The diagonal and Hermitian
identities are required on the whole ambient function space. -/
structure Sesq (Q : (ι → ℂ) → ℝ) (B : (ι → ℂ) → (ι → ℂ) → ℂ) (D : Submodule ℂ (ι → ℂ)) :
    Prop where
  self : ∀ u : ι → ℂ, B u u = (Q u : ℂ)
  addL : ∀ {a b v : ι → ℂ}, a ∈ D → b ∈ D → v ∈ D → B (a + b) v = B a v + B b v
  addR : ∀ {a v w : ι → ℂ}, a ∈ D → v ∈ D → w ∈ D → B a (v + w) = B a v + B a w
  conj : ∀ u v : ι → ℂ, B v u = (starRingEnd ℂ) (B u v)
  smulR : ∀ {a v : ι → ℂ} (c : ℂ), a ∈ D → v ∈ D → B a (c • v) = c * B a v

namespace Sesq

variable {Q : (ι → ℂ) → ℝ} {B : (ι → ℂ) → (ι → ℂ) → ℂ} {D : Submodule ℂ (ι → ℂ)}

lemma zero_right (h : Sesq Q B D) {a : ι → ℂ} (ha : a ∈ D) : B a 0 = 0 := by
  have := h.addR ha D.zero_mem D.zero_mem
  rw [add_zero] at this
  linear_combination -this

lemma zero_left (h : Sesq Q B D) {v : ι → ℂ} (hv : v ∈ D) : B 0 v = 0 := by
  rw [h.conj, h.zero_right hv, map_zero]

lemma Q_zero (h : Sesq Q B D) : Q 0 = 0 := by
  have := h.self 0
  rw [h.zero_right D.zero_mem] at this
  exact_mod_cast this.symm

lemma smulL (h : Sesq Q B D) {a v : ι → ℂ} (c : ℂ) (ha : a ∈ D) (hv : v ∈ D) :
    B (c • a) v = (starRingEnd ℂ) c * B a v := by
  rw [h.conj, h.smulR c hv ha, map_mul, ← h.conj]

/-- Restriction of the structure to a subdomain. -/
lemma mono (h : Sesq Q B D) {D' : Submodule ℂ (ι → ℂ)} (hD' : D' ≤ D) : Sesq Q B D' where
  self := h.self
  addL := fun ha hb hv => h.addL (hD' ha) (hD' hb) (hD' hv)
  addR := fun ha hv hw => h.addR (hD' ha) (hD' hv) (hD' hw)
  conj := h.conj
  smulR := fun c ha hv => h.smulR c (hD' ha) (hD' hv)

lemma Q_smul (h : Sesq Q B D) {v : ι → ℂ} (c : ℂ) (hv : v ∈ D) :
    Q (c • v) = ‖c‖ ^ 2 * Q v := by
  have hc : (Q (c • v) : ℂ) = ‖c‖ ^ 2 * (Q v : ℂ) := by
    rw [← h.self, h.smulR c (D.smul_mem c hv) hv, h.smulL c hv hv, h.self, ← mul_assoc,
      Complex.mul_conj, Complex.normSq_eq_norm_sq]
    push_cast; ring
  exact_mod_cast hc

/-- `B` against a finite sum of domain vectors in the second slot. -/
lemma sum_right (h : Sesq Q B D) {a : ι → ℂ} (ha : a ∈ D) {β : Type*} (s : Finset β)
    {v : β → ι → ℂ} (hv : ∀ j ∈ s, v j ∈ D) :
    B a (∑ j ∈ s, v j) = ∑ j ∈ s, B a (v j) := by
  induction s using Finset.induction_on with
  | empty => simp [h.zero_right ha]
  | insert j s hj ih =>
    rw [Finset.sum_insert hj, Finset.sum_insert hj,
      h.addR ha (hv j (Finset.mem_insert_self j s))
        (D.sum_mem fun i hi => hv i (Finset.mem_insert_of_mem hi)),
      ih fun i hi => hv i (Finset.mem_insert_of_mem hi)]

/-- `B` against a finite sum of domain vectors in the first slot. -/
lemma sum_left (h : Sesq Q B D) {v : ι → ℂ} (hv : v ∈ D) {β : Type*} (s : Finset β)
    {a : β → ι → ℂ} (ha : ∀ j ∈ s, a j ∈ D) :
    B (∑ j ∈ s, a j) v = ∑ j ∈ s, B (a j) v := by
  rw [h.conj, h.sum_right hv s ha, map_sum]
  exact Finset.sum_congr rfl fun j _ => (h.conj v (a j)).symm

/-- **Block-diagonal energy**: the energy of a finite sum of pairwise `B`-orthogonal domain vectors
is the sum of the energies. -/
lemma Q_sum (h : Sesq Q B D) {β : Type*} (s : Finset β) {v : β → ι → ℂ}
    (hv : ∀ j ∈ s, v j ∈ D) (horth : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → B (v i) (v j) = 0) :
    Q (∑ j ∈ s, v j) = ∑ j ∈ s, Q (v j) := by
  have hc : (Q (∑ j ∈ s, v j) : ℂ) = ∑ j ∈ s, (Q (v j) : ℂ) := by
    rw [← h.self, h.sum_left (D.sum_mem hv) s hv]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [h.sum_right (hv i hi) s hv,
      Finset.sum_eq_single i (fun j hj hji => horth i hi j hj (Ne.symm hji))
        (fun hi' => absurd hi hi'),
      h.self]
  exact_mod_cast hc

end Sesq

/-! ### Orthogonal decompositions of the domain -/

/-- A finite `B`-orthogonal direct-sum decomposition of the domain `D` into blocks `Dblk j`,
with linear block projections `P j` (`P j v ∈ Dblk j`, `∑ j, P j v = v`, and `P j` kills the
other blocks).  For a character decomposition, `P j` is the averaging projection. -/
structure OrthDecomp (B : (ι → ℂ) → (ι → ℂ) → ℂ) (D : Submodule ℂ (ι → ℂ))
    {β : Type*} [Fintype β] (Dblk : β → Submodule ℂ (ι → ℂ)) where
  le : ∀ j, Dblk j ≤ D
  orth : ∀ i j, i ≠ j → ∀ u ∈ Dblk i, ∀ v ∈ Dblk j, B u v = 0
  P : β → (↥D →ₗ[ℂ] (ι → ℂ))
  P_mem : ∀ j (v : ↥D), P j v ∈ Dblk j
  P_sum : ∀ v : ↥D, ∑ j, P j v = (v : ι → ℂ)
  P_ne : ∀ i j, i ≠ j → ∀ v : ↥D, (v : ι → ℂ) ∈ Dblk i → P j v = 0

namespace OrthDecomp

variable {B : (ι → ℂ) → (ι → ℂ) → ℂ} {D : Submodule ℂ (ι → ℂ)}
  {β : Type*} [Fintype β] {Dblk : β → Submodule ℂ (ι → ℂ)}

lemma P_mem_D (hd : OrthDecomp B D Dblk) (j : β) (v : ↥D) : hd.P j v ∈ D :=
  hd.le j (hd.P_mem j v)

/-- `P i` is the identity on its own block. -/
lemma P_self (hd : OrthDecomp B D Dblk) {i : β} (v : ↥D) (hv : (v : ι → ℂ) ∈ Dblk i) :
    hd.P i v = v := by
  have := hd.P_sum v
  rw [Finset.sum_eq_single i (fun j _ hji => hd.P_ne i j (Ne.symm hji) v hv)
    (fun hi => absurd (Finset.mem_univ i) hi)] at this
  exact this

/-- `x ↦ ∑ j, x j` from the external direct sum of block subspaces `V j`. -/
def sumMap (V : β → Submodule ℂ (ι → ℂ)) : ((j : β) → ↥(V j)) →ₗ[ℂ] (ι → ℂ) :=
  ∑ j, (V j).subtype.comp (LinearMap.proj j)

lemma sumMap_apply (V : β → Submodule ℂ (ι → ℂ)) (x : (j : β) → ↥(V j)) :
    sumMap V x = ∑ j, (x j : ι → ℂ) := by
  simp [sumMap, LinearMap.sum_apply]

/-- The external direct sum of block subspaces injects into `D` (the projections separate it). -/
lemma sumMap_injective (hd : OrthDecomp B D Dblk) {V : β → Submodule ℂ (ι → ℂ)}
    (hV : ∀ j, V j ≤ Dblk j) : Function.Injective (sumMap V) := by
  rw [← LinearMap.ker_eq_bot, eq_bot_iff]
  intro x hx
  rw [Submodule.mem_bot]
  have h0 : sumMap V x = 0 := LinearMap.mem_ker.mp hx
  rw [sumMap_apply] at h0
  let lift : β → ↥D := fun j => ⟨(x j : ι → ℂ), hd.le j (hV j (x j).2)⟩
  have hlift : (∑ j, lift j : ↥D) = 0 := by
    apply Subtype.ext
    rw [Submodule.coe_sum, Submodule.coe_zero]
    exact h0
  funext i
  have h1 : hd.P i (∑ j, lift j) = (x i : ι → ℂ) := by
    rw [map_sum, Finset.sum_eq_single i (fun j _ hji => hd.P_ne j i hji (lift j) (hV j (x j).2))
      (fun hi => absurd (Finset.mem_univ i) hi)]
    exact hd.P_self (lift i) (hV i (x i).2)
  rw [hlift, map_zero] at h1
  exact Subtype.ext h1.symm

end OrthDecomp

/-! ### Monotonicity and attainment -/

lemma formIndex_mono {Q : (ι → ℂ) → ℝ} {D D' : Submodule ℂ (ι → ℂ)} (h : D' ≤ D) :
    formIndex Q D' ≤ formIndex Q D := by
  refine iSup_le fun V => iSup_le fun hV => iSup_le fun hfd => ?_
  exact le_iSup_of_le V (le_iSup_of_le ⟨le_trans hV.1 h, hV.2⟩ (le_iSup_of_le hfd le_rfl))

lemma NegOn_bot (Q : (ι → ℂ) → ℝ) (D : Submodule ℂ (ι → ℂ)) : NegOn Q D ⊥ :=
  ⟨bot_le, fun u hu hune => absurd ((Submodule.mem_bot ℂ).mp hu) hune⟩

lemma NullOn_bot {Q : (ι → ℂ) → ℝ} {B : (ι → ℂ) → (ι → ℂ) → ℂ} {D : Submodule ℂ (ι → ℂ)}
    (h : Sesq Q B D) : NullOn B D ⊥ :=
  ⟨bot_le, fun _ hu _ hv => by rw [(Submodule.mem_bot ℂ).mp hu, h.zero_left hv]⟩

/-- **A finite supremum of finranks is attained.** -/
lemma exists_finrank_eq_of_biSup {p : Submodule ℂ (ι → ℂ) → Prop} (hbot : p ⊥) {n : ℕ}
    (hn : (⨆ (V : Submodule ℂ (ι → ℂ)) (_ : p V ∧ FiniteDimensional ℂ V),
      (finrank ℂ V : ℕ∞)) = n) :
    ∃ V : Submodule ℂ (ι → ℂ), p V ∧ FiniteDimensional ℂ V ∧ finrank ℂ V = n := by
  have : Nonempty {V : Submodule ℂ (ι → ℂ) // p V ∧ FiniteDimensional ℂ V} :=
    ⟨⟨⊥, hbot, inferInstance⟩⟩
  rw [iSup_subtype'] at hn
  have hlt := lt_of_eq_of_lt hn (WithTop.coe_lt_top n)
  obtain ⟨V, hV⟩ := ENat.exists_eq_iSup_of_lt_top hlt
  refine ⟨V, V.2.1, V.2.2, ?_⟩
  rw [hn] at hV
  exact_mod_cast hV

lemma exists_negOn_finrank_eq {Q : (ι → ℂ) → ℝ} {D : Submodule ℂ (ι → ℂ)} {n : ℕ}
    (hn : formIndex Q D = n) :
    ∃ V : Submodule ℂ (ι → ℂ), NegOn Q D V ∧ FiniteDimensional ℂ V ∧ finrank ℂ V = n := by
  rw [formIndex_eq_biSup] at hn
  exact exists_finrank_eq_of_biSup (NegOn_bot Q D) hn

lemma exists_nullOn_finrank_eq {Q : (ι → ℂ) → ℝ} {B : (ι → ℂ) → (ι → ℂ) → ℂ}
    {D : Submodule ℂ (ι → ℂ)} (h : Sesq Q B D) {n : ℕ} (hn : formNullity B D = n) :
    ∃ V : Submodule ℂ (ι → ℂ), NullOn B D V ∧ FiniteDimensional ℂ V ∧ finrank ℂ V = n := by
  rw [formNullity_eq_biSup] at hn
  exact exists_finrank_eq_of_biSup (NullOn_bot h) hn

/-! ### The maximal-negative complement is nonnegative -/

/-- **Complement of a maximal negative subspace.**  If `formIndex Q D = n` and `N ≤ D` is negative
with `finrank N = n`, then every `v ∈ D` that is `B`-orthogonal to `N` has `Q v ≥ 0`.  (Otherwise
`N ⊔ span{v}` is negative of dimension `n + 1`.) -/
lemma nonneg_of_orth_maximal {Q : (ι → ℂ) → ℝ} {B : (ι → ℂ) → (ι → ℂ) → ℂ}
    {D : Submodule ℂ (ι → ℂ)} (h : Sesq Q B D) {n : ℕ} (hn : formIndex Q D = n)
    {N : Submodule ℂ (ι → ℂ)} (hN : NegOn Q D N) [FiniteDimensional ℂ N]
    (hNfr : finrank ℂ N = n) {v : ι → ℂ} (hv : v ∈ D) (horth : ∀ u ∈ N, B u v = 0) :
    0 ≤ Q v := by
  by_contra hlt
  rw [not_le] at hlt
  have hv0 : v ≠ 0 := fun h0 => by rw [h0, h.Q_zero] at hlt; exact lt_irrefl _ hlt
  -- `v ∉ N`: a vector of `N` orthogonal to itself has zero energy
  have hvN : v ∉ N := fun hvN => by
    have h1 := horth v hvN
    rw [h.self] at h1
    have h2 : Q v = 0 := by exact_mod_cast h1
    linarith
  have hdisj : N ⊓ Submodule.span ℂ {v} = ⊥ := by
    rw [eq_bot_iff]
    intro u hu
    obtain ⟨huN, huS⟩ := Submodule.mem_inf.mp hu
    rw [Submodule.mem_span_singleton] at huS
    obtain ⟨c, rfl⟩ := huS
    rw [Submodule.mem_bot]
    rcases eq_or_ne c 0 with rfl | hc
    · simp
    · exfalso
      apply hvN
      have := N.smul_mem c⁻¹ huN
      rwa [smul_smul, inv_mul_cancel₀ hc, one_smul] at this
  have hspan_le : Submodule.span ℂ {v} ≤ D := by
    rw [Submodule.span_le, Set.singleton_subset_iff]; exact hv
  -- `N ⊔ span{v}` is negative
  have hWneg : NegOn Q D (N ⊔ Submodule.span ℂ {v}) := by
    refine ⟨sup_le hN.1 hspan_le, ?_⟩
    intro u hu hune
    obtain ⟨a, haN, b, hbS, rfl⟩ := Submodule.mem_sup.mp hu
    rw [Submodule.mem_span_singleton] at hbS
    obtain ⟨c, rfl⟩ := hbS
    have haD : a ∈ D := hN.1 haN
    have hcvD : c • v ∈ D := D.smul_mem c hv
    have hcross : B a (c • v) = 0 := by rw [h.smulR c haD hv, horth a haN, mul_zero]
    have hcross' : B (c • v) a = 0 := by rw [h.conj, hcross, map_zero]
    have hQ : Q (a + c • v) = Q a + ‖c‖ ^ 2 * Q v := by
      have hc : (Q (a + c • v) : ℂ) = (Q a : ℂ) + (Q (c • v) : ℂ) := by
        rw [← h.self, h.addL haD hcvD (D.add_mem haD hcvD), h.addR haD haD hcvD,
          h.addR hcvD haD hcvD, hcross, hcross', h.self, h.self]
        ring
      have h' : Q (a + c • v) = Q a + Q (c • v) := by exact_mod_cast hc
      rw [h', h.Q_smul c hv]
    rw [hQ]
    have hQa : Q a ≤ 0 := by
      rcases eq_or_ne a 0 with rfl | ha
      · rw [h.Q_zero]
      · exact le_of_lt (hN.2 a haN ha)
    rcases eq_or_ne c 0 with rfl | hc
    · have ha : a ≠ 0 := by simpa using hune
      have h1 := hN.2 a haN ha
      have h0 : ‖(0 : ℂ)‖ ^ 2 * Q v = 0 := by simp
      linarith
    · have hpos : 0 < ‖c‖ ^ 2 := by positivity
      have := mul_neg_of_pos_of_neg hpos hlt
      linarith
  have : FiniteDimensional ℂ (Submodule.span ℂ {v}) :=
    FiniteDimensional.span_of_finite _ (Set.finite_singleton v)
  have hfr : finrank ℂ (N ⊔ Submodule.span ℂ {v} : Submodule ℂ (ι → ℂ)) = n + 1 := by
    have h1 := Submodule.finrank_sup_add_finrank_inf_eq N (Submodule.span ℂ {v})
    rw [hdisj, finrank_bot, add_zero, hNfr, finrank_span_singleton hv0] at h1
    exact h1
  have hle : ((n + 1 : ℕ) : ℕ∞) ≤ formIndex Q D := by
    rw [← hfr]
    exact le_iSup_of_le _ (le_iSup_of_le hWneg (le_iSup_of_le inferInstance le_rfl))
  rw [hn] at hle
  have : n + 1 ≤ n := by exact_mod_cast hle
  omega

/-! ### Index additivity -/

section Additivity

variable {Q : (ι → ℂ) → ℝ} {B : (ι → ℂ) → (ι → ℂ) → ℂ} {D : Submodule ℂ (ι → ℂ)}
  {β : Type*} [Fintype β] {Dblk : β → Submodule ℂ (ι → ℂ)}

/-- **Index superadditivity**: `∑ j, ind(Dblk j) ≤ ind(D)`. -/
theorem sum_formIndex_le (h : Sesq Q B D) (hd : OrthDecomp B D Dblk) :
    ∑ j, formIndex Q (Dblk j) ≤ formIndex Q D := by
  by_cases htop : ∃ j, formIndex Q (Dblk j) = ⊤
  · obtain ⟨j, hj⟩ := htop
    have h1 : formIndex Q (Dblk j) ≤ formIndex Q D := formIndex_mono (hd.le j)
    rw [hj] at h1
    rw [top_le_iff.mp h1]
    exact le_top
  push Not at htop
  choose n hn using fun j => ENat.ne_top_iff_exists.mp (htop j)
  choose V hV using fun j => exists_negOn_finrank_eq (hn j).symm
  have : ∀ j, FiniteDimensional ℂ (V j) := fun j => (hV j).2.1
  have hVle : ∀ j, V j ≤ Dblk j := fun j => (hV j).1.1
  set L := OrthDecomp.sumMap V with hL
  have hinj : Function.Injective L := hd.sumMap_injective hVle
  set W := LinearMap.range L with hW
  have hWfd : FiniteDimensional ℂ W := inferInstance
  have hWfr : finrank ℂ W = ∑ j, n j := by
    rw [hW, LinearMap.finrank_range_of_inj hinj, Module.finrank_pi_fintype]
    exact Finset.sum_congr rfl fun j _ => (hV j).2.2
  have hWneg : NegOn Q D W := by
    refine ⟨?_, ?_⟩
    · rintro _ ⟨x, rfl⟩
      rw [hL, OrthDecomp.sumMap_apply]
      exact D.sum_mem fun j _ => hd.le j (hVle j (x j).2)
    · rintro _ ⟨x, rfl⟩ hne
      have hx : x ≠ 0 := fun h0 => hne (by rw [h0, map_zero])
      rw [hL, OrthDecomp.sumMap_apply]
      have hmem : ∀ j ∈ Finset.univ, ((x j : ι → ℂ)) ∈ D :=
        fun j _ => hd.le j (hVle j (x j).2)
      have horth : ∀ i ∈ Finset.univ, ∀ j ∈ Finset.univ, i ≠ j →
          B (x i : ι → ℂ) (x j : ι → ℂ) = 0 :=
        fun i _ j _ hij => hd.orth i j hij _ (hVle i (x i).2) _ (hVle j (x j).2)
      rw [h.Q_sum Finset.univ hmem horth]
      have hle : ∀ j ∈ Finset.univ, Q (x j : ι → ℂ) ≤ 0 := fun j _ => by
        rcases eq_or_ne (x j) 0 with h0 | h0
        · rw [h0]; simp [h.Q_zero]
        · exact le_of_lt ((hV j).1.2 _ (x j).2 (fun h' => h0 (Subtype.ext h')))
      refine lt_of_le_of_ne (Finset.sum_nonpos hle) fun hzero => hx ?_
      rw [Finset.sum_eq_zero_iff_of_nonpos hle] at hzero
      funext j
      by_contra hj
      have h1 := (hV j).1.2 _ (x j).2 (fun h' => hj (Subtype.ext h'))
      linarith [hzero j (Finset.mem_univ j)]
  calc ∑ j, formIndex Q (Dblk j) = ∑ j, (n j : ℕ∞) :=
        Finset.sum_congr rfl fun j _ => (hn j).symm
    _ = ((∑ j, n j : ℕ) : ℕ∞) := by rw [Nat.cast_sum]
    _ = (finrank ℂ W : ℕ∞) := by rw [hWfr]
    _ ≤ formIndex Q D :=
        le_iSup_of_le W (le_iSup_of_le hWneg (le_iSup_of_le hWfd le_rfl))

/-- **Index subadditivity**: `ind(D) ≤ ∑ j, ind(Dblk j)`.  The dual-map argument, with each
block's functionals evaluated on a basis of its maximal negative subspace. -/
theorem formIndex_le_sum (h : Sesq Q B D) (hd : OrthDecomp B D Dblk) :
    formIndex Q D ≤ ∑ j, formIndex Q (Dblk j) := by
  by_cases htop : ∃ j, formIndex Q (Dblk j) = ⊤
  · obtain ⟨j, hj⟩ := htop
    rw [ENat.sum_eq_top.mpr ⟨j, Finset.mem_univ j, hj⟩]
    exact le_top
  push Not at htop
  choose n hn using fun j => ENat.ne_top_iff_exists.mp (htop j)
  choose N hN using fun j => exists_negOn_finrank_eq (hn j).symm
  have : ∀ j, FiniteDimensional ℂ (N j) := fun j => (hN j).2.1
  have hNle : ∀ j, N j ≤ D := fun j => le_trans (hN j).1.1 (hd.le j)
  -- complement nonnegativity in each block
  have hcomp : ∀ j, ∀ v ∈ Dblk j, (∀ u ∈ N j, B u v = 0) → 0 ≤ Q v := fun j v hv hu =>
    nonneg_of_orth_maximal (h.mono (hd.le j)) (hn j).symm (hN j).1 (hN j).2.2 hv hu
  -- a basis of each maximal negative block
  let bas : (j : β) → Basis (Fin (n j)) ℂ (N j) :=
    fun j => Module.finBasisOfFinrankEq ℂ (N j) (hN j).2.2
  refine iSup_le fun V => iSup_le fun hV => iSup_le fun hfd => ?_
  have := hfd
  let emb : ↥V →ₗ[ℂ] ↥D := Submodule.inclusion hV.1
  -- the block-functional map `w ↦ (B (b_i^j) (P j w))_{j,i}`
  let T : ↥V →ₗ[ℂ] ((j : β) → (Fin (n j) → ℂ)) :=
    { toFun := fun w j i => B (bas j i : ι → ℂ) (hd.P j (emb w))
      map_add' := fun w w' => by
        funext j i
        simp only [map_add, Pi.add_apply]
        exact h.addR (hNle j (bas j i).2) (hd.P_mem_D j (emb w)) (hd.P_mem_D j (emb w'))
      map_smul' := fun c w => by
        funext j i
        simp only [map_smul, Pi.smul_apply, RingHom.id_apply, smul_eq_mul]
        exact h.smulR c (hNle j (bas j i).2) (hd.P_mem_D j (emb w)) }
  have hT : Function.Injective T := by
    rw [← LinearMap.ker_eq_bot, eq_bot_iff]
    intro w hw
    rw [Submodule.mem_bot]
    have h0 : T w = 0 := LinearMap.mem_ker.mp hw
    -- each block component is `B`-orthogonal to the whole of `N j`
    have horthN : ∀ j, ∀ u ∈ N j, B u (hd.P j (emb w)) = 0 := by
      intro j u hu
      have hrep0 : (⟨u, hu⟩ : ↥(N j)) = ∑ i, (bas j).repr ⟨u, hu⟩ i • bas j i :=
        ((bas j).sum_repr ⟨u, hu⟩).symm
      have hrep : u = ∑ i, (bas j).repr ⟨u, hu⟩ i • (bas j i : ι → ℂ) := by
        have h' := congrArg Subtype.val hrep0
        rw [Submodule.coe_sum] at h'
        simpa only [Submodule.coe_smul] using h'
      rw [hrep, h.sum_left (hd.P_mem_D j (emb w)) Finset.univ
        (fun i _ => D.smul_mem _ (hNle j (bas j i).2))]
      refine Finset.sum_eq_zero fun i _ => ?_
      rw [h.smulL _ (hNle j (bas j i).2) (hd.P_mem_D j (emb w))]
      have hTi : B (bas j i : ι → ℂ) (hd.P j (emb w)) = 0 := congrFun (congrFun h0 j) i
      rw [hTi, mul_zero]
    have hQge : 0 ≤ Q (w : ι → ℂ) := by
      have hsum : (w : ι → ℂ) = ∑ j, hd.P j (emb w) := (hd.P_sum (emb w)).symm
      rw [hsum, h.Q_sum Finset.univ (fun j _ => hd.P_mem_D j (emb w))
        (fun i _ j _ hij => hd.orth i j hij _ (hd.P_mem i _) _ (hd.P_mem j _))]
      exact Finset.sum_nonneg fun j _ => hcomp j _ (hd.P_mem j (emb w)) (horthN j)
    by_contra hne
    have hne' : (w : ι → ℂ) ≠ 0 := fun h' => hne (Subtype.ext h')
    linarith [hV.2 _ w.2 hne']
  have hfin : finrank ℂ ↥V ≤ finrank ℂ ((j : β) → (Fin (n j) → ℂ)) :=
    LinearMap.finrank_le_finrank_of_injective hT
  rw [Module.finrank_pi_fintype] at hfin
  simp only [Module.finrank_fin_fun] at hfin
  calc (finrank ℂ ↥V : ℕ∞) ≤ ((∑ j, n j : ℕ) : ℕ∞) := by exact_mod_cast hfin
    _ = ∑ j, (n j : ℕ∞) := by rw [Nat.cast_sum]
    _ = ∑ j, formIndex Q (Dblk j) := Finset.sum_congr rfl fun j _ => hn j

/-- **Index additivity over an orthogonal decomposition.** -/
theorem formIndex_eq_sum (h : Sesq Q B D) (hd : OrthDecomp B D Dblk) :
    formIndex Q D = ∑ j, formIndex Q (Dblk j) :=
  le_antisymm (formIndex_le_sum h hd) (sum_formIndex_le h hd)

/-! ### Nullity additivity -/

/-- A block radical is a `D`-radical: every `D`-vector splits into block components, each paired
to zero (own block: radical; other blocks: orthogonality). -/
lemma nullOn_of_block (h : Sesq Q B D) (hd : OrthDecomp B D Dblk) {j : β}
    {V : Submodule ℂ (ι → ℂ)} (hV : NullOn B (Dblk j) V) : NullOn B D V := by
  refine ⟨le_trans hV.1 (hd.le j), fun u hu y hy => ?_⟩
  have key : (∑ i, hd.P i ⟨y, hy⟩) = y := hd.P_sum ⟨y, hy⟩
  rw [← key, h.sum_right (hd.le j (hV.1 hu)) Finset.univ (fun i _ => hd.P_mem_D i ⟨y, hy⟩)]
  refine Finset.sum_eq_zero fun i _ => ?_
  rcases eq_or_ne i j with rfl | hij
  · exact hV.2 u hu _ (hd.P_mem i _)
  · exact hd.orth j i (Ne.symm hij) u (hV.1 hu) _ (hd.P_mem i _)

lemma formNullity_block_le (h : Sesq Q B D) (hd : OrthDecomp B D Dblk) (j : β) :
    formNullity B (Dblk j) ≤ formNullity B D := by
  refine iSup_le fun V => iSup_le fun hV => iSup_le fun hfd => ?_
  exact le_iSup_of_le V (le_iSup_of_le (nullOn_of_block h hd hV) (le_iSup_of_le hfd le_rfl))

/-- **Nullity superadditivity**: `∑ j, nul(Dblk j) ≤ nul(D)`. -/
theorem sum_formNullity_le (h : Sesq Q B D) (hd : OrthDecomp B D Dblk) :
    ∑ j, formNullity B (Dblk j) ≤ formNullity B D := by
  by_cases htop : ∃ j, formNullity B (Dblk j) = ⊤
  · obtain ⟨j, hj⟩ := htop
    have h1 := formNullity_block_le h hd j
    rw [hj] at h1
    rw [top_le_iff.mp h1]
    exact le_top
  push Not at htop
  choose n hn using fun j => ENat.ne_top_iff_exists.mp (htop j)
  choose V hV using fun j => exists_nullOn_finrank_eq (h.mono (hd.le j)) (hn j).symm
  have : ∀ j, FiniteDimensional ℂ (V j) := fun j => (hV j).2.1
  have hVle : ∀ j, V j ≤ Dblk j := fun j => (hV j).1.1
  set L := OrthDecomp.sumMap V with hL
  have hinj : Function.Injective L := hd.sumMap_injective hVle
  set W := LinearMap.range L with hW
  have hWfd : FiniteDimensional ℂ W := inferInstance
  have hWfr : finrank ℂ W = ∑ j, n j := by
    rw [hW, LinearMap.finrank_range_of_inj hinj, Module.finrank_pi_fintype]
    exact Finset.sum_congr rfl fun j _ => (hV j).2.2
  have hWnull : NullOn B D W := by
    refine ⟨?_, ?_⟩
    · rintro _ ⟨x, rfl⟩
      rw [hL, OrthDecomp.sumMap_apply]
      exact D.sum_mem fun j _ => hd.le j (hVle j (x j).2)
    · rintro _ ⟨x, rfl⟩ y hy
      rw [hL, OrthDecomp.sumMap_apply,
        h.sum_left hy Finset.univ (fun j _ => hd.le j (hVle j (x j).2))]
      exact Finset.sum_eq_zero fun j _ => (nullOn_of_block h hd (hV j).1).2 _ (x j).2 y hy
  calc ∑ j, formNullity B (Dblk j) = ∑ j, (n j : ℕ∞) :=
        Finset.sum_congr rfl fun j _ => (hn j).symm
    _ = ((∑ j, n j : ℕ) : ℕ∞) := by rw [Nat.cast_sum]
    _ = (finrank ℂ W : ℕ∞) := by rw [hWfr]
    _ ≤ formNullity B D :=
        le_iSup_of_le W (le_iSup_of_le hWnull (le_iSup_of_le hWfd le_rfl))

/-- **Nullity subadditivity**: `nul(D) ≤ ∑ j, nul(Dblk j)`.  The projections carry a `D`-radical
into block radicals; `w ↦ (P j w)_j` is injective since `∑ P j = id`. -/
theorem formNullity_le_sum (h : Sesq Q B D) (hd : OrthDecomp B D Dblk) :
    formNullity B D ≤ ∑ j, formNullity B (Dblk j) := by
  refine iSup_le fun V => iSup_le fun hV => iSup_le fun hfd => ?_
  have := hfd
  let emb : ↥V →ₗ[ℂ] ↥D := Submodule.inclusion hV.1
  let g : (j : β) → (↥V →ₗ[ℂ] (ι → ℂ)) := fun j => (hd.P j).comp emb
  let Vj : β → Submodule ℂ (ι → ℂ) := fun j => LinearMap.range (g j)
  have hVjfd : ∀ j, FiniteDimensional ℂ (Vj j) := fun j => LinearMap.finiteDimensional_range (g j)
  have hVjnull : ∀ j, NullOn B (Dblk j) (Vj j) := by
    intro j
    refine ⟨?_, ?_⟩
    · rintro _ ⟨p, rfl⟩
      exact hd.P_mem j (emb p)
    · rintro _ ⟨p, rfl⟩ y hy
      have key : (∑ i, hd.P i (emb p)) = (p : ι → ℂ) := hd.P_sum (emb p)
      have h0 : B (p : ι → ℂ) y = 0 := hV.2 _ p.2 y (hd.le j hy)
      rw [← key, h.sum_left (hd.le j hy) Finset.univ (fun i _ => hd.P_mem_D i (emb p)),
        Finset.sum_eq_single j (fun i _ hij => hd.orth i j hij _ (hd.P_mem i _) y hy)
          (fun hj => absurd (Finset.mem_univ j) hj)] at h0
      exact h0
  let G : ↥V →ₗ[ℂ] ((j : β) → ↥(Vj j)) :=
    LinearMap.pi fun j => (g j).codRestrict (Vj j) (fun x => LinearMap.mem_range_self (g j) x)
  have hG : Function.Injective G := by
    rw [← LinearMap.ker_eq_bot, eq_bot_iff]
    intro x hx
    rw [Submodule.mem_bot]
    have h0 : G x = 0 := LinearMap.mem_ker.mp hx
    have hcomp : ∀ j, hd.P j (emb x) = 0 := fun j => congrArg Subtype.val (congrFun h0 j)
    have hsum := hd.P_sum (emb x)
    simp only [hcomp, Finset.sum_const_zero] at hsum
    exact Subtype.ext hsum.symm
  have hfin : finrank ℂ ↥V ≤ finrank ℂ ((j : β) → ↥(Vj j)) :=
    LinearMap.finrank_le_finrank_of_injective hG
  rw [Module.finrank_pi_fintype] at hfin
  calc (finrank ℂ ↥V : ℕ∞) ≤ ((∑ j, finrank ℂ (Vj j) : ℕ) : ℕ∞) := by exact_mod_cast hfin
    _ = ∑ j, (finrank ℂ (Vj j) : ℕ∞) := by rw [Nat.cast_sum]
    _ ≤ ∑ j, formNullity B (Dblk j) :=
        Finset.sum_le_sum fun j _ =>
          le_iSup_of_le (Vj j) (le_iSup_of_le (hVjnull j) (le_iSup_of_le (hVjfd j) le_rfl))

/-- **Nullity additivity over an orthogonal decomposition.** -/
theorem formNullity_eq_sum (h : Sesq Q B D) (hd : OrthDecomp B D Dblk) :
    formNullity B D = ∑ j, formNullity B (Dblk j) :=
  le_antisymm (formNullity_le_sum h hd) (sum_formNullity_le h hd)

end Additivity

end KsIndex.FormIndex
