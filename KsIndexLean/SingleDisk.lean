module

/-
# Single-disk domains and seam index transport

`SingleCc k b₁ b₀` describes the disk functions obtained by restricting
the even or odd copy-swap eigenspaces of the one-period pair domains.
On `arc_1`, the sign `sgn b₁` determines smooth even or odd reflection
through the unit circle. The odd case also requires zero assigned values
on the entire circle. On `arc_0`, `b₀ = true` requires a one-sided smooth
extension, while `b₀ = false` requires vanishing near the closed slit.
Both cases require smoothness on the open disk, zero values outside the
closed disk and vanishing near the punctures.

The two arc families therefore use different boundary encodings. A screw
rotation exchanges their locations but does not by itself identify the
two mixed `SingleCc` spaces. Comparison with the arc-uniform natural
spaces is a separate step.

`formIndex_transport_surj` transports index along a form-preserving
surjection without assuming injectivity on the whole domain: its kernel
intersects every negative subspace trivially. `seam_transport` applies
this result for `k ≥ 1` and a unit rotation multiplier. Restriction to
copy zero has the signed extension `extS` as a right inverse. This
extension uses `sgn b₁ * f` on the second open disk and `f` on its circle
and exterior, matching the total-function convention of the copy swap.
The pair form is twice the single-disk form, which leaves index unchanged.

Finally, `indSurface_seam_bracket` bounds the surface index by sums of
the Dirichlet-slit and Neumann-slit seam quantities over rotation classes
and translation sectors, for `k ≥ 2` and positive period count `m`.
-/
public import KsIndexLean.Bracket
public import KsIndexLean.SingleDiskBridge

@[expose] public section


noncomputable section

open Complex Real MeasureTheory Filter Topology
open scoped ContDiff

/-! ### Kernel-tolerant Morse-index transport -/

namespace KsIndex.FormIndex

/-- **Index transport without injectivity.**  If `L` maps `D` onto `D'`, carries `Q` to `Q'` on
`D`, and `Q' 0 = 0`, then `formIndex Q D = formIndex Q' D'`: a negative subspace meets the kernel
of `L` trivially (the form vanishes there), so it maps injectively; conversely a negative subspace
of `D'` lifts by lifting a basis. -/
theorem formIndex_transport_surj {ι κ : Type*} (L : (ι → ℂ) →ₗ[ℂ] (κ → ℂ))
    {Q : (ι → ℂ) → ℝ} {Q' : (κ → ℂ) → ℝ}
    {D : Submodule ℂ (ι → ℂ)} {D' : Submodule ℂ (κ → ℂ)}
    (hmap : ∀ u ∈ D, L u ∈ D')
    (hsurj : ∀ w ∈ D', ∃ u ∈ D, L u = w)
    (hform : ∀ u ∈ D, Q u = Q' (L u)) (h0 : Q' 0 = 0) :
    formIndex Q D = formIndex Q' D' := by
  apply le_antisymm
  · refine iSup_le fun V => iSup_le fun hV => iSup_le fun hfd => ?_
    have := hfd
    -- `L` is injective on the negative subspace `V`
    have hinjV : ∀ u ∈ V, ∀ v ∈ V, L u = L v → u = v := by
      intro u hu v hv huv
      by_contra hne
      have hmem : u - v ∈ V := V.sub_mem hu hv
      have hne' : u - v ≠ 0 := sub_ne_zero.mpr hne
      have hneg := hV.2 (u - v) hmem hne'
      rw [hform (u - v) (hV.1 hmem), map_sub, huv, sub_self, h0] at hneg
      exact lt_irrefl _ hneg
    have : FiniteDimensional ℂ ↥(V.map L) :=
      Module.Finite.equiv (KsIndex.SectorIndex.mapEquiv L hinjV le_rfl)
    have hneg : NegOn Q' D' (V.map L) := by
      refine ⟨Submodule.map_le_iff_le_comap.mpr fun u hu => hmap u (hV.1 hu), ?_⟩
      intro w hw hwne
      obtain ⟨u, huV, rfl⟩ := Submodule.mem_map.mp hw
      have hune : u ≠ 0 := fun h => hwne (by rw [h, map_zero])
      rw [← hform u (hV.1 huV)]
      exact hV.2 u huV hune
    have hfr : (Module.finrank ℂ V : ℕ∞) = Module.finrank ℂ ↥(V.map L) := by
      rw [(KsIndex.SectorIndex.mapEquiv L hinjV le_rfl).finrank_eq]
    rw [hfr]
    exact le_iSup_of_le (V.map L) (le_iSup_of_le hneg (le_iSup_of_le ‹_› le_rfl))
  · refine iSup_le fun V' => iSup_le fun hV' => iSup_le fun hfd' => ?_
    have := hfd'
    obtain ⟨n, hn⟩ : ∃ n, Module.finrank ℂ V' = n := ⟨_, rfl⟩
    let b := Module.finBasisOfFinrankEq ℂ V' hn
    choose u hu using fun i => hsurj (b i) (hV'.1 (b i).2)
    have hcomp : (⇑L ∘ u) = fun i => ((b i : V') : κ → ℂ) := funext fun i => (hu i).2
    have hbli : LinearIndependent ℂ fun i => ((b i : V') : κ → ℂ) :=
      b.linearIndependent.map' V'.subtype V'.ker_subtype
    have huli : LinearIndependent ℂ u := LinearIndependent.of_comp L (by rw [hcomp]; exact hbli)
    set V : Submodule ℂ (ι → ℂ) := Submodule.span ℂ (Set.range u) with hVdef
    have hVD : V ≤ D := Submodule.span_le.mpr (by rintro _ ⟨i, rfl⟩; exact (hu i).1)
    have hVfin : FiniteDimensional ℂ V := FiniteDimensional.span_of_finite ℂ (Set.finite_range u)
    have hfrV : Module.finrank ℂ V = n := by
      rw [hVdef, finrank_span_eq_card huli, Fintype.card_fin]
    have hLV : ∀ v ∈ V, L v ∈ V' := by
      have hle : V ≤ V'.comap L := by
        refine Submodule.span_le.mpr ?_
        rintro _ ⟨i, rfl⟩
        rw [SetLike.mem_coe, Submodule.mem_comap, (hu i).2]
        exact (b i).2
      exact fun v hv => Submodule.mem_comap.mp (hle hv)
    have hLinj : ∀ v ∈ V, L v = 0 → v = 0 := by
      intro v hv hLv
      obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).mp hv
      have hsum : ∑ i, c i • ((b i : V') : κ → ℂ) = 0 := by
        rw [← hLv, map_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [map_smul, (hu i).2]
      have hc := Fintype.linearIndependent_iff.mp hbli c hsum
      simp [hc]
    have hneg : NegOn Q D V := by
      refine ⟨hVD, ?_⟩
      intro v hv hvne
      have hLne : L v ≠ 0 := fun h => hvne (hLinj v hv h)
      rw [hform v (hVD hv)]
      exact hV'.2 (L v) (hLV v hv) hLne
    have hfr : (Module.finrank ℂ V' : ℕ∞) = Module.finrank ℂ V := by rw [hn, hfrV]
    rw [hfr]
    exact le_iSup_of_le V (le_iSup_of_le hneg (le_iSup_of_le hVfin le_rfl))

end KsIndex.FormIndex

namespace KsIndex.SingleDisk

open KsIndex.Surface KsIndex.SurfaceForm KsIndex.SurfaceSym KsIndex.FormIndex KsIndex.Twisted
  KsIndex.Bracket KsIndex.SingleDiskBridge KsIndex.GradOrtho

variable {k : ℕ}

/-! ### Reflections, signs, single-copy support conditions -/

/-- The reflection of `f` through the circle with sign `s`: `f` on the closed disk, `s · f ∘ σ`
outside.  `s = 1` is the even (Neumann) reflection, `s = −1` the odd (Dirichlet) one. -/
def refl (s : ℂ) (f : ℂ → ℂ) (z : ℂ) : ℂ := if ‖z‖ ≤ 1 then f z else s * f (σ z)

lemma refl_add (s : ℂ) (f g : ℂ → ℂ) : refl s (f + g) = refl s f + refl s g := by
  funext z; simp only [refl, Pi.add_apply]; split_ifs <;> ring

lemma refl_smul (s c : ℂ) (f : ℂ → ℂ) : refl s (c • f) = c • refl s f := by
  funext z; simp only [refl, Pi.smul_apply, smul_eq_mul]; split_ifs <;> ring

lemma refl_zero (s : ℂ) : refl s (0 : ℂ → ℂ) = 0 := by
  funext z; simp only [refl, Pi.zero_apply, mul_zero]; split_ifs <;> rfl

/-- The sign of a parity flag: `sgn true = 1`, `sgn false = −1`. -/
def sgn (b : Bool) : ℂ := if b then 1 else -1

@[simp] lemma sgn_true : sgn true = 1 := rfl
@[simp] lemma sgn_false : sgn false = -1 := rfl

lemma norm_sgn (b : Bool) : ‖sgn b‖ = 1 := by cases b <;> simp [sgn]
lemma sgn_mul_sgn (b : Bool) : sgn b * sgn b = 1 := by cases b <;> simp [sgn]
lemma sgn_ne_zero (b : Bool) : sgn b ≠ 0 := by cases b <;> simp [sgn]

/-- Vanishing near the punctures (one copy). -/
def SuppAwayP1 (k : ℕ) (f : ℂ → ℂ) : Prop :=
  ∃ ε > 0, ∀ w, (∃ p ∈ punctures k, ‖w - p‖ < ε) → f w = 0

/-- Vanishing near the closed slit (one copy). -/
def SuppAwaySlit1 (k : ℕ) (f : ℂ → ℂ) : Prop :=
  ∃ ε > 0, ∀ w, (∃ p ∈ slit k, ‖w - p‖ < ε) → f w = 0

lemma suppAwayP1_of_slit (hk : 1 ≤ k) {f : ℂ → ℂ} (h : SuppAwaySlit1 k f) : SuppAwayP1 k f := by
  obtain ⟨ε, hε, h⟩ := h
  exact ⟨ε, hε, fun w ⟨p, hp, hwp⟩ => h w ⟨p, punctures_subset_slit hk hp, hwp⟩⟩

/-- The condition on the slit `arc_0`: Neumann (`b₀ = true`, one-sided smooth extension) or
Dirichlet (`b₀ = false`, vanishing near the closed slit). -/
def Arc0Cond (k : ℕ) : Bool → (ℂ → ℂ) → Prop
  | true, f => ∀ w ∈ arc k 0, OneSided f w
  | false, f => SuppAwaySlit1 k f

/-- The single-disk smoothness/boundary package with parity `b₁` across `arc_1` and condition
`b₀` on `arc_0`. -/
def IsSmoothS (k : ℕ) (b₁ b₀ : Bool) (f : ℂ → ℂ) : Prop :=
  ContDiffOn ℝ ∞ f disk
    ∧ (∀ w ∈ arc k 1, ContDiffAt ℝ ∞ (refl (sgn b₁) f) w)
    ∧ Arc0Cond k b₀ f
    ∧ (∀ w, 1 < ‖w‖ → f w = 0)
    ∧ (b₁ = false → ∀ w, ‖w‖ = 1 → f w = 0)
    ∧ SuppAwayP1 k f

lemma arc0Cond_zero (k : ℕ) (b₀ : Bool) : Arc0Cond k b₀ 0 := by
  cases b₀
  · exact ⟨1, one_pos, fun _ _ => rfl⟩
  · exact fun w _ => oneSided_zero w

lemma arc0Cond_add {b₀ : Bool} {f g : ℂ → ℂ} (hf : Arc0Cond k b₀ f) (hg : Arc0Cond k b₀ g) :
    Arc0Cond k b₀ (f + g) := by
  cases b₀
  · obtain ⟨ε₁, h₁, hf⟩ := hf
    obtain ⟨ε₂, h₂, hg⟩ := hg
    refine ⟨min ε₁ ε₂, lt_min h₁ h₂, fun w ⟨p, hp, hwp⟩ => ?_⟩
    simp only [Pi.add_apply, hf w ⟨p, hp, lt_of_lt_of_le hwp (min_le_left _ _)⟩,
      hg w ⟨p, hp, lt_of_lt_of_le hwp (min_le_right _ _)⟩, add_zero]
  · exact fun w hw => oneSided_add (hf w hw) (hg w hw)

lemma arc0Cond_smul {b₀ : Bool} (c : ℂ) {f : ℂ → ℂ} (hf : Arc0Cond k b₀ f) :
    Arc0Cond k b₀ (c • f) := by
  cases b₀
  · obtain ⟨ε, hε, hf⟩ := hf
    exact ⟨ε, hε, fun w hw => by simp only [Pi.smul_apply, hf w hw, smul_zero]⟩
  · exact fun w hw => oneSided_smul c (hf w hw)

lemma isSmoothS_zero (k : ℕ) (b₁ b₀ : Bool) : IsSmoothS k b₁ b₀ 0 := by
  refine ⟨contDiffOn_const, fun w _ => ?_, arc0Cond_zero k b₀, fun _ _ => rfl, fun _ _ _ => rfl,
    ⟨1, one_pos, fun _ _ => rfl⟩⟩
  rw [refl_zero]; exact contDiffAt_const

lemma isSmoothS_add {b₁ b₀ : Bool} {f g : ℂ → ℂ} (hf : IsSmoothS k b₁ b₀ f)
    (hg : IsSmoothS k b₁ b₀ g) : IsSmoothS k b₁ b₀ (f + g) := by
  obtain ⟨f1, f2, f3, f4, f5, ⟨ε₁, h₁, f6⟩⟩ := hf
  obtain ⟨g1, g2, g3, g4, g5, ⟨ε₂, h₂, g6⟩⟩ := hg
  refine ⟨f1.add g1, fun w hw => ?_, arc0Cond_add f3 g3, fun w hw => ?_, fun hb w hw => ?_,
    ⟨min ε₁ ε₂, lt_min h₁ h₂, fun w ⟨p, hp, hwp⟩ => ?_⟩⟩
  · rw [refl_add]; exact (f2 w hw).add (g2 w hw)
  · simp only [Pi.add_apply, f4 w hw, g4 w hw, add_zero]
  · simp only [Pi.add_apply, f5 hb w hw, g5 hb w hw, add_zero]
  · simp only [Pi.add_apply, f6 w ⟨p, hp, lt_of_lt_of_le hwp (min_le_left _ _)⟩,
      g6 w ⟨p, hp, lt_of_lt_of_le hwp (min_le_right _ _)⟩, add_zero]

lemma isSmoothS_smul {b₁ b₀ : Bool} (c : ℂ) {f : ℂ → ℂ} (hf : IsSmoothS k b₁ b₀ f) :
    IsSmoothS k b₁ b₀ (c • f) := by
  obtain ⟨f1, f2, f3, f4, f5, ⟨ε, hε, f6⟩⟩ := hf
  refine ⟨f1.const_smul c, fun w hw => ?_, arc0Cond_smul c f3, fun w hw => ?_, fun hb w hw => ?_,
    ⟨ε, hε, fun w hw => ?_⟩⟩
  · rw [refl_smul]; exact (f2 w hw).const_smul c
  · simp only [Pi.smul_apply, f4 w hw, smul_zero]
  · simp only [Pi.smul_apply, f5 hb w hw, smul_zero]
  · simp only [Pi.smul_apply, f6 w hw, smul_zero]

/-- **The single-disk test space**: parity `b₁` across `arc_1`, condition `b₀` on the slit. -/
def SingleCc (k : ℕ) (b₁ b₀ : Bool) : Submodule ℂ (ℂ → ℂ) where
  carrier := {f | IsSmoothS k b₁ b₀ f}
  zero_mem' := isSmoothS_zero k b₁ b₀
  add_mem' := fun hf hg => isSmoothS_add hf hg
  smul_mem' := fun c _ hf => isSmoothS_smul c hf

lemma mem_SingleCc {b₁ b₀ : Bool} {f : ℂ → ℂ} : f ∈ SingleCc k b₁ b₀ ↔ IsSmoothS k b₁ b₀ f :=
  Iff.rfl

/-- The pair space carrying condition `b₀` on the slit: `DomN` (`true`) or `DomD` (`false`). -/
def DomPair (k : ℕ) : Bool → Submodule ℂ (ZMod (2 * 1) × ℂ → ℂ)
  | true => DomN k
  | false => DomD k

/-! ### Restriction to copy `0` and the signed extension -/

/-- Restriction of a pair to copy `0`. -/
def res0 : (ZMod (2 * 1) × ℂ → ℂ) →ₗ[ℂ] (ℂ → ℂ) where
  toFun U := fun w => U (0, w)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] lemma res0_apply (U : ZMod (2 * 1) × ℂ → ℂ) (w : ℂ) : res0 U w = U (0, w) := rfl

/-- The signed extension of a single-disk function to a pair: copy `0` is `f`; copy `1` is
`s · f` on the open disk and `f` on the circle and outside (the circle-value convention of
`swapF`). -/
def extS (s : ℂ) : (ℂ → ℂ) →ₗ[ℂ] (ZMod (2 * 1) × ℂ → ℂ) where
  toFun f := fun p => if p.1 = 0 then f p.2 else (if ‖p.2‖ < 1 then s * f p.2 else f p.2)
  map_add' _ _ := by
    funext p
    simp only [Pi.add_apply]
    split_ifs <;> ring
  map_smul' _ _ := by
    funext p
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    split_ifs <;> ring

lemma extS_zero (s : ℂ) (f : ℂ → ℂ) (w : ℂ) : extS s f (0, w) = f w := by
  simp [extS]

lemma extS_one (s : ℂ) (f : ℂ → ℂ) (w : ℂ) :
    extS s f (1, w) = if ‖w‖ < 1 then s * f w else f w := by
  simp [extS, show (1 : ZMod (2 * 1)) ≠ 0 by decide]

lemma res0_extS (s : ℂ) (f : ℂ → ℂ) : res0 (extS s f) = f :=
  funext fun w => extS_zero s f w

lemma zmod_two_cases (n : ZMod (2 * 1)) : n = 0 ∨ n = 1 := by revert n; decide

/-- The swap eigen-condition, pointwise. -/
lemma mem_swap_iff {s : ℂ} {U : ZMod (2 * 1) × ℂ → ℂ} :
    U ∈ Module.End.eigenspace swapE s
      ↔ ∀ p : ZMod (2 * 1) × ℂ, (if ‖p.2‖ < 1 then U (p.1 + 1, p.2) else U p) = s * U p := by
  rw [Module.End.mem_eigenspace_iff]
  have e : ∀ q : ZMod (2 * 1) × ℂ,
      swapE U q = if ‖q.2‖ < 1 then U (q.1 + 1, q.2) else U q := fun _ => rfl
  constructor
  · intro h p
    rw [← e p]
    exact congr_fun h p
  · intro h
    funext p
    rw [e p]
    exact h p

lemma norm_σ_lt {z : ℂ} (hz : 1 < ‖z‖) : ‖σ z‖ < 1 := by
  rw [norm_σ]
  exact (inv_lt_one₀ (lt_trans one_pos hz)).mpr hz

/-! ### Restriction lands in the single-disk space -/

lemma res_mem (hk : 1 ≤ k) {b₁ b₀ : Bool} {a μ : ℂ} {U : ZMod (2 * 1) × ℂ → ℂ}
    (hU : U ∈ (DomPair k b₀ ⊓ Module.End.eigenspace (rotE 1 a) μ)
      ⊓ Module.End.eigenspace swapE (sgn b₁)) :
    res0 U ∈ SingleCc k b₁ b₀ ⊓ Module.End.eigenspace (rot1 a) μ := by
  obtain ⟨⟨hD, hR⟩, hS₀⟩ := hU
  have hS := mem_swap_iff.mp hS₀
  refine Submodule.mem_inf.mpr ⟨?_, ?_⟩
  swap
  · have hR' := Module.End.mem_eigenspace_iff.mp hR
    rw [Module.End.mem_eigenspace_iff]
    funext w
    exact congr_fun hR' (0, w)
  -- the pair facts, uniformly in `b₀`
  set v := (uncurryE 1).symm U with hv
  have hpair : (∀ n, ContDiffOn ℝ ∞ (v n) disk)
      ∧ (∀ w ∈ seamArc k 1 0, ContDiffAt ℝ ∞ (glue v 0) w)
      ∧ Arc0Cond k b₀ (v 0) ∧ (∀ n w, 1 < ‖w‖ → v n w = 0) ∧ SuppAwayP k 1 v := by
    cases b₀
    · obtain ⟨⟨h1, h2, h4⟩, hsl⟩ := mem_DomD.mp hD
      refine ⟨h1, h2, ?_, h4, suppAwayP_of_slit hk hsl⟩
      obtain ⟨ε, hε, hz⟩ := hsl
      exact ⟨ε, hε, fun w hw => hz 0 w hw⟩
    · obtain ⟨⟨h1, h2, h3, h4⟩, hp⟩ := mem_DomN.mp hD
      exact ⟨h1, h2, h3 0, h4, hp⟩
  obtain ⟨h1, h2, h3, h4, ⟨ε, hε, hp⟩⟩ := hpair
  have hres : res0 U = v 0 := rfl
  have hrefl : refl (sgn b₁) (v 0) = glue v 0 := by
    funext z
    simp only [refl, glue, zero_add]
    split_ifs with hz
    · rfl
    · have hgt : 1 < ‖z‖ := not_le.mp hz
      have hlt : ‖σ z‖ < 1 := norm_σ_lt hgt
      have := hS (0, σ z)
      dsimp only at this
      rw [if_pos hlt, zero_add] at this
      rw [show (1 / (starRingEnd ℂ) z) = σ z from rfl]
      exact this.symm
  rw [hres, mem_SingleCc]
  refine ⟨h1 0, fun w hw => ?_, h3, h4 0, fun hb w hw => ?_, ⟨ε, hε, fun w hw => hp 0 w hw⟩⟩
  · rw [hrefl]
    exact h2 w (by rwa [seamArc_one_zero])
  · subst hb
    have := hS (0, w)
    dsimp only at this
    rw [if_neg (not_lt.mpr (le_of_eq hw.symm)), sgn_false] at this
    -- `U (0, w) = -1 * U (0, w)`
    have h2v : (2 : ℂ) * v 0 w = 0 := by
      change (2 : ℂ) * U (0, w) = 0
      linear_combination this
    exact (mul_eq_zero.mp h2v).resolve_left two_ne_zero

/-! ### Extension lands in the pair space -/

lemma extS_mem_pair {b₁ b₀ : Bool} {f : ℂ → ℂ} (hf : f ∈ SingleCc k b₁ b₀) :
    extS (sgn b₁) f ∈ DomPair k b₀ := by
  obtain ⟨f1, f2, f3, f4, f5, ⟨ε, hε, f6⟩⟩ := mem_SingleCc.mp hf
  set s := sgn b₁ with hs
  set v := (uncurryE 1).symm (extS s f) with hv
  have hv0 : v 0 = f := funext fun w => extS_zero s f w
  have hv1 : ∀ w, v 1 w = if ‖w‖ < 1 then s * f w else f w := fun w => extS_one s f w
  have hv1disk : ∀ w ∈ disk, v 1 w = s * f w := fun w hw => by
    rw [hv1, if_pos (mem_disk_iff.mp hw)]
  -- the ingredients shared by both pair spaces
  have hsm : ∀ n, ContDiffOn ℝ ∞ (v n) disk := by
    intro n
    rcases zmod_two_cases n with rfl | rfl
    · rw [hv0]; exact f1
    · exact (f1.const_smul s).congr fun w hw => by rw [hv1disk w hw]; rfl
  have hglue : glue v 0 = refl s f := by
    funext z
    simp only [glue, refl, zero_add, hv0]
    split_ifs with hz
    · rfl
    · rw [show (1 / (starRingEnd ℂ) z) = σ z from rfl, hv1disk _ (mem_disk_iff.mpr
        (norm_σ_lt (not_le.mp hz)))]
  have hseam : ∀ w ∈ seamArc k 1 0, ContDiffAt ℝ ∞ (glue v 0) w := by
    intro w hw
    rw [hglue]
    exact f2 w (by rwa [seamArc_one_zero] at hw)
  have hout : ∀ n w, 1 < ‖w‖ → v n w = 0 := by
    intro n w hw
    rcases zmod_two_cases n with rfl | rfl
    · rw [hv0]; exact f4 w hw
    · rw [hv1, if_neg (not_lt.mpr (le_of_lt hw))]; exact f4 w hw
  have hpunct : SuppAwayP k 1 v := by
    refine ⟨ε, hε, fun n w hw => ?_⟩
    rcases zmod_two_cases n with rfl | rfl
    · rw [hv0]; exact f6 w hw
    · rw [hv1]; split_ifs <;> simp [f6 w hw]
  cases b₀
  · -- Dirichlet: vanishing near the closed slit
    obtain ⟨δ, hδ, hsl⟩ := f3
    have hvmem : v ∈ DCc k := by
      refine ⟨⟨hsm, hseam, hout⟩, ⟨δ, hδ, fun n w hw => ?_⟩⟩
      rcases zmod_two_cases n with rfl | rfl
      · rw [hv0]; exact hsl w hw
      · rw [hv1]; split_ifs <;> simp [hsl w hw]
    exact mem_DomD.mpr hvmem
  · -- Neumann: one-sided extensions at the slit
    have hvmem : v ∈ NCc k := by
      refine ⟨⟨hsm, hseam, fun n w hw => ?_, hout⟩, hpunct⟩
      rcases zmod_two_cases n with rfl | rfl
      · rw [hv0]; exact f3 w hw
      · obtain ⟨F, hF, hFe⟩ := f3 w hw
        refine ⟨fun z => s * F z, contDiffAt_const.mul hF, ?_⟩
        filter_upwards [hFe] with z h hz
        rw [hv1disk z hz, h hz]
    exact mem_DomN.mpr hvmem

lemma extS_mem_rot {a μ : ℂ} (ha : ‖a‖ = 1) {s : ℂ} {f : ℂ → ℂ}
    (hf : f ∈ Module.End.eigenspace (rot1 a) μ) :
    extS s f ∈ Module.End.eigenspace (rotE 1 a) μ := by
  rw [Module.End.mem_eigenspace_iff] at hf ⊢
  have hcomm : rotE 1 a (extS s f) = extS s (rot1 a f) := by
    funext p
    simp only [rotE_apply, extS, LinearMap.coe_mk, AddHom.coe_mk, rot1_apply, norm_mul, ha,
      one_mul]
  rw [hcomm, hf, map_smul]

lemma extS_mem_swap {b₁ b₀ : Bool} {f : ℂ → ℂ} (hf : f ∈ SingleCc k b₁ b₀) :
    extS (sgn b₁) f ∈ Module.End.eigenspace swapE (sgn b₁) := by
  obtain ⟨-, -, -, f4, f5, -⟩ := mem_SingleCc.mp hf
  rw [mem_swap_iff]
  rintro ⟨n, w⟩
  simp only
  by_cases hw : ‖w‖ < 1
  · rw [if_pos hw]
    rcases zmod_two_cases n with rfl | rfl
    · rw [zero_add, extS_one, if_pos hw, extS_zero]
    · rw [one_add_one_zmod, extS_zero, extS_one, if_pos hw, ← mul_assoc, sgn_mul_sgn, one_mul]
  · rw [if_neg hw]
    -- on the circle and outside: `f w = sgn b₁ · f w`
    have hfw : f w = sgn b₁ * f w := by
      rcases lt_or_eq_of_le (not_lt.mp hw) with h | h
      · rw [f4 w h, mul_zero]
      · cases b₁
        · rw [f5 rfl w h.symm, mul_zero]
        · rw [sgn_true, one_mul]
    rcases zmod_two_cases n with rfl | rfl
    · rw [extS_zero]; exact hfw
    · rw [extS_one, if_neg hw]; exact hfw

/-! ### The form: `jacobiQ k 1 (f, s·f) = 2 · Qd k f` -/

lemma dirichletG_congr_disk {f g : ℂ → ℂ} (h : ∀ w ∈ disk, f w = g w) :
    dirichletG k f = dirichletG k g := by
  unfold dirichletG
  refine setIntegral_congr_fun measurableSet_disk fun w hw => ?_
  have he : f =ᶠ[𝓝 w] g := eventually_of_mem (Metric.isOpen_ball.mem_nhds hw) h
  simp only [gradSq, he.fderiv_eq]

lemma potentialG_congr_disk {f g : ℂ → ℂ} (h : ∀ w ∈ disk, f w = g w) :
    potentialG k f = potentialG k g := by
  unfold potentialG
  refine setIntegral_congr_fun measurableSet_disk fun w hw => ?_
  simp only [h w hw]

lemma Qd_zero (k : ℕ) : Qd k 0 = 0 := by
  simp [Qd, dirichletG, potentialG, gradSq]

lemma Qs_eq_two_Qd {s : ℂ} (hs : ‖s‖ = 1) {U : ZMod (2 * 1) × ℂ → ℂ}
    (hS : U ∈ Module.End.eigenspace swapE s) :
    Qs k 1 U = 2 * Qd k (res0 U) := by
  have hS' := mem_swap_iff.mp hS
  simp only [Qs, jacobiQ]
  rw [sum_zmod_two]
  set v := (uncurryE 1).symm U with hv
  have h01 : ∀ w ∈ disk, v 1 w = s * v 0 w := by
    intro w hw
    have := hS' (0, w)
    dsimp only at this
    rw [if_pos (mem_disk_iff.mp hw), zero_add] at this
    exact this
  have hres : res0 U = v 0 := rfl
  have h1 : dirichletG k (v 1) - potentialG k (v 1) = dirichletG k (v 0) - potentialG k (v 0) := by
    rw [dirichletG_congr_disk h01, potentialG_congr_disk h01]
    exact summand_unit_mul k hs _
  rw [h1, hres, Qd]
  ring

/-! ### The four seam transports -/

/-- **Seam transport.**  The `sgn b₁`-swap-part of the pair problem with slit condition `b₀`, on
the rotation eigenspace `E_rot(a, μ)`, has the index of the one-disk form on
`SingleCc k b₁ b₀ ⊓ E_rot1(a, μ)`.  (`b₁ = even?` across `arc_1`, `b₀ = Neumann?` on `arc_0`.) -/
theorem seam_transport (hk : 1 ≤ k) (b₁ b₀ : Bool) {a μ : ℂ} (ha : ‖a‖ = 1) :
    formIndex (Qs k 1) ((DomPair k b₀ ⊓ Module.End.eigenspace (rotE 1 a) μ)
        ⊓ Module.End.eigenspace swapE (sgn b₁))
      = formIndex (Qd k) (SingleCc k b₁ b₀ ⊓ Module.End.eigenspace (rot1 a) μ) := by
  rw [← formIndex_smul_pos (Q := Qd k)
    (D := SingleCc k b₁ b₀ ⊓ Module.End.eigenspace (rot1 a) μ) (two_pos : (0 : ℝ) < 2)]
  refine formIndex_transport_surj res0 (fun U hU => ?_) (fun f hf => ?_) (fun U hU => ?_) ?_
  · exact res_mem hk hU
  · obtain ⟨hf1, hf2⟩ := Submodule.mem_inf.mp hf
    refine ⟨extS (sgn b₁) f, ?_, res0_extS _ _⟩
    exact Submodule.mem_inf.mpr ⟨Submodule.mem_inf.mpr ⟨extS_mem_pair (k := k) hf1,
      extS_mem_rot ha hf2⟩, extS_mem_swap (k := k) hf1⟩
  · exact Qs_eq_two_Qd (norm_sgn b₁) hU.2
  · rw [Qd_zero, mul_zero]

/-! ### `ind(Ξ_{k,m})` bracketed by the seam quantities -/

/-- The class-`r` rotation eigenspace on single-disk functions. -/
def Erot1 (k : ℕ) (r : ℕ) : Submodule ℂ (ℂ → ℂ) :=
  Module.End.eigenspace (rot1 (rotUnit k : ℂ)) (zeta k ^ r)

/-- The four seam quantities of class `r`: `ind(Qd k)` on `SingleCc k b₁ b₀ ⊓ Erot1 k r`. -/
def seam (k : ℕ) (b₁ b₀ : Bool) (r : ℕ) : ℕ∞ :=
  formIndex (Qd k) (SingleCc k b₁ b₀ ⊓ Erot1 k r)

/-- **`ind(Ξ_{k,m})` is bracketed by the seam quantities**: over the rotation classes `r < k` and
flux sectors `s < m`, the sum of the two Dirichlet-slit seam quantities (even and odd across the
seam arc) is a lower bound and the sum of the two Neumann-slit ones an upper bound,
for `k ≥ 2` and `m > 0`. The seam quantities are defined here; their evaluation
is supplied separately. -/
theorem indSurface_seam_bracket {m : ℕ} [NeZero m] (hk : 2 ≤ k) :
    (∑ r : Fin k, ∑ _s : Fin m, (seam k true false r + seam k false false r))
        ≤ indSurface k m
      ∧ indSurface k m
        ≤ ∑ r : Fin k, ∑ _s : Fin m, (seam k true true r + seam k false true r) := by
  have hm : 0 < m := Nat.pos_of_ne_zero (NeZero.ne m)
  have ha : ‖(rotUnit k : ℂ)‖ = 1 := Circle.norm_coe _
  rw [indSurface_eq_sum_sectors hk]
  have key : ∀ (r : Fin k) (s : Fin m),
      seam k true false r + seam k false false r
        ≤ formIndex (Qs k m) ((Dom k m ⊓ Module.End.eigenspace (rotE m (rotUnit k : ℂ))
            (zeta k ^ (r : ℕ))) ⊓ Module.End.eigenspace (shiftE m) (zeta m ^ (s : ℕ)))
      ∧ formIndex (Qs k m) ((Dom k m ⊓ Module.End.eigenspace (rotE m (rotUnit k : ℂ))
            (zeta k ^ (r : ℕ))) ⊓ Module.End.eigenspace (shiftE m) (zeta m ^ (s : ℕ)))
        ≤ seam k true true r + seam k false true r := by
    intro r s
    have hζ : ‖zeta m ^ (s : ℕ)‖ = 1 := by
      rw [norm_pow, (zeta_prim hm).norm'_eq_one hm.ne', one_pow]
    have hζm : (zeta m ^ (s : ℕ)) ^ m = 1 := by
      rw [← pow_mul, mul_comm, pow_mul, zeta_pow_N hm, one_pow]
    have hζ0 : zeta m ^ (s : ℕ) ≠ 0 := by
      intro h; rw [h, norm_zero] at hζ; exact zero_ne_one hζ
    rw [formIndex_sector_eq hζ hζm]
    obtain ⟨hlo, hhi⟩ := formIndex_bracket (k := k) (by omega) hζ0
      (Module.End.eigenspace (rotE 1 (rotUnit k : ℂ)) (zeta k ^ (r : ℕ)))
    rw [formIndex_D_split hk ha] at hlo
    rw [formIndex_N_split hk ha] at hhi
    have e1 := seam_transport (k := k) (by omega) true false (μ := zeta k ^ (r : ℕ)) ha
    have e2 := seam_transport (k := k) (by omega) false false (μ := zeta k ^ (r : ℕ)) ha
    have e3 := seam_transport (k := k) (by omega) true true (μ := zeta k ^ (r : ℕ)) ha
    have e4 := seam_transport (k := k) (by omega) false true (μ := zeta k ^ (r : ℕ)) ha
    simp only [sgn_true, sgn_false, DomPair] at e1 e2 e3 e4
    simp only [seam, Erot1]
    rw [e1, e2] at hlo
    rw [e3, e4] at hhi
    exact ⟨hlo, hhi⟩
  constructor
  · exact Finset.sum_le_sum fun r _ => Finset.sum_le_sum fun s _ => (key r s).1
  · exact Finset.sum_le_sum fun r _ => Finset.sum_le_sum fun s _ => (key r s).2

end KsIndex.SingleDisk
