module

/-
KsIndexLean — SectorIndex: eigenspace domains and index/nullity transport.

The two submodules inside the sector domain `Domς` are

    Dtan α = {u ∈ Domς : R_α u = −u},
    Dcot α = {u ∈ Domς : R_α u = u}.

When `1+cos(απ) ≠ 0` and `1−cos(απ) ≠ 0`, respectively, restriction to
the `inl` coordinates identifies these domains with `CircleQ.MemDom` and
carries `NQform` to twice the circle form at `coefT α` or `coefC α`.
The restriction map is globally linear; its injectivity and inverse formulas
are assertions on the relevant domains, whose membership includes summability.

Generic transport lemmas use `Submodule.map` and `Submodule.comap`. The
index-additivity proof here uses the rank-at-most-one bounds for each circle
block and orthogonal projections onto negative directions. Nullity additivity
uses the radical decomposition given by the two eigenprojections. Both final
identities require the two nonzero-denominator hypotheses.

`SectorPhase` uses this module's nullity identity and the separate spectral
index-additivity theorem from `SectorSpectralAdditivity`, then rewrites the
parameters as tangent and cotangent for the phase counts.
-/
public import KsIndexLean.SectorReduce
public import KsIndexLean.FormIndex
public import KsIndexLean.FormIndexBridge

@[expose] public section


noncomputable section

namespace KsIndex.SectorIndex

open KsIndex.CircleQ KsIndex.SIsometry KsIndex.Sector KsIndex.SectorForm
  KsIndex.SectorReduce KsIndex.FormIndex KsIndex.Statements KsIndex.FormIndexBridge

/-- `R_α` fixes `0`. -/
lemma rop_zero (α : ℝ) : rop α (0 : Idx → ℂ) = 0 := by
  have h : rop α ((0 : ℂ) • (0 : Idx → ℂ)) = (0 : ℂ) • rop α (0 : Idx → ℂ) :=
    rop_smul α 0 0
  simpa using h

/-- `SectorL2` of a domain vector (helper to feed `rop_add`). -/
lemma sectorL2_of_mem_Domς {u : Idx → ℂ} (hu : u ∈ Domς) : SectorL2 u :=
  memSector_sectorL2 (mem_Domς.mp hu).1

/-! ### The `tan`-block eigenspace `ker(R_α + I) ∩ Domς` -/

/-- The `tan` block: `{u ∈ Domς : R_α u = −u}`.  A submodule because `R_α` is
`ℂ`-linear on `Domς`. -/
def Dtan (α : ℝ) : Submodule ℂ (Idx → ℂ) where
  carrier := {u | u ∈ Domς ∧ rop α u = -u}
  zero_mem' := ⟨Domς.zero_mem, by rw [rop_zero, neg_zero]⟩
  add_mem' := by
    rintro u v ⟨hu, hru⟩ ⟨hv, hrv⟩
    exact ⟨Domς.add_mem hu hv, by
      rw [rop_add α (sectorL2_of_mem_Domς hu) (sectorL2_of_mem_Domς hv), hru, hrv, neg_add]⟩
  smul_mem' := by
    rintro c u ⟨hu, hru⟩
    exact ⟨Domς.smul_mem c hu, by rw [rop_smul, hru, smul_neg]⟩

/-- The `cot` block: `{u ∈ Domς : R_α u = u}`. -/
def Dcot (α : ℝ) : Submodule ℂ (Idx → ℂ) where
  carrier := {u | u ∈ Domς ∧ rop α u = u}
  zero_mem' := ⟨Domς.zero_mem, rop_zero α⟩
  add_mem' := by
    rintro u v ⟨hu, hru⟩ ⟨hv, hrv⟩
    exact ⟨Domς.add_mem hu hv, by
      rw [rop_add α (sectorL2_of_mem_Domς hu) (sectorL2_of_mem_Domς hv), hru, hrv]⟩
  smul_mem' := by
    rintro c u ⟨hu, hru⟩
    exact ⟨Domς.smul_mem c hu, by rw [rop_smul, hru]⟩

@[simp] lemma mem_Dtan {α : ℝ} {u : Idx → ℂ} :
    u ∈ Dtan α ↔ u ∈ Domς ∧ rop α u = -u := Iff.rfl

@[simp] lemma mem_Dcot {α : ℝ} {u : Idx → ℂ} :
    u ∈ Dcot α ↔ u ∈ Domς ∧ rop α u = u := Iff.rfl

lemma Dtan_le_Domς (α : ℝ) : Dtan α ≤ Domς := fun _ hu => hu.1
lemma Dcot_le_Domς (α : ℝ) : Dcot α ≤ Domς := fun _ hu => hu.1

/-! ### Generic Morse-index transport along an injective-on-domain linear map

If a linear map `L` is injective on a domain `D`, maps `D` onto `D'`, and carries
the form `Q` to `Q'` there, then `formIndex Q D = formIndex Q' D'`.  The transport
rides on `Submodule.map`/`comap`; `L` need not be globally injective (only on `D`),
which is exactly the situation for `restrictL` (globally linear, injective only on
the eigenspaces).  Generic in the two coordinate types. -/

/-- Each `V ≤ D` is linearly isomorphic to its image `V.map L`, when `L` is
injective on `D`. -/
noncomputable def mapEquiv {ι κ : Type*} (L : (ι → ℂ) →ₗ[ℂ] (κ → ℂ))
    {D : Submodule ℂ (ι → ℂ)} (hinj : ∀ u ∈ D, ∀ v ∈ D, L u = L v → u = v)
    {V : Submodule ℂ (ι → ℂ)} (hVD : V ≤ D) : V ≃ₗ[ℂ] ↥(V.map L) :=
  have hdr : Function.Injective (L.domRestrict V) := by
    intro x y hxy
    apply Subtype.ext
    exact hinj x (hVD x.2) y (hVD y.2) (by simpa [LinearMap.domRestrict_apply] using hxy)
  (LinearEquiv.ofInjective (L.domRestrict V) hdr).trans
    (LinearEquiv.ofEq _ _ (LinearMap.range_domRestrict V L))

theorem formIndex_transport {ι κ : Type*} (L : (ι → ℂ) →ₗ[ℂ] (κ → ℂ))
    {Q : (ι → ℂ) → ℝ} {Q' : (κ → ℂ) → ℝ}
    {D : Submodule ℂ (ι → ℂ)} {D' : Submodule ℂ (κ → ℂ)}
    (hmap : ∀ u ∈ D, L u ∈ D')
    (hinj : ∀ u ∈ D, ∀ v ∈ D, L u = L v → u = v)
    (hsurj : ∀ w ∈ D', ∃ u ∈ D, L u = w)
    (hform : ∀ u ∈ D, Q u = Q' (L u)) :
    formIndex Q D = formIndex Q' D' := by
  apply le_antisymm
  · refine iSup_le fun V => iSup_le fun hV => iSup_le fun hfd => ?_
    have := hfd
    have : FiniteDimensional ℂ ↥(V.map L) := Module.Finite.equiv (mapEquiv L hinj hV.1)
    have hneg : NegOn Q' D' (V.map L) := by
      refine ⟨Submodule.map_le_iff_le_comap.mpr fun u hu => hmap u (hV.1 hu), ?_⟩
      intro w hw hwne
      obtain ⟨u, huV, rfl⟩ := Submodule.mem_map.mp hw
      have hune : u ≠ 0 := fun h => hwne (by rw [h, map_zero])
      rw [← hform u (hV.1 huV)]
      exact hV.2 u huV hune
    have hfr : (Module.finrank ℂ V : ℕ∞) = Module.finrank ℂ ↥(V.map L) := by
      rw [(mapEquiv L hinj hV.1).finrank_eq]
    rw [hfr]
    exact le_iSup_of_le (V.map L) (le_iSup_of_le hneg (le_iSup_of_le ‹_› le_rfl))
  · refine iSup_le fun V' => iSup_le fun hV' => iSup_le fun hfd' => ?_
    have := hfd'
    set V := (V'.comap L) ⊓ D with hVdef
    have hVD : V ≤ D := inf_le_right
    have hmapV : V.map L = V' := by
      apply le_antisymm
      · exact Submodule.map_le_iff_le_comap.mpr fun u hu => (Submodule.mem_inf.mp hu).1
      · intro w hw
        obtain ⟨u, huD, hLuw⟩ := hsurj w (hV'.1 hw)
        refine Submodule.mem_map.mpr ⟨u, Submodule.mem_inf.mpr
          ⟨Submodule.mem_comap.mpr (by rw [hLuw]; exact hw), huD⟩, hLuw⟩
    have : FiniteDimensional ℂ ↥(V.map L) := hmapV ▸ hfd'
    have : FiniteDimensional ℂ V := Module.Finite.equiv (mapEquiv L hinj hVD).symm
    have hneg : NegOn Q D V := by
      refine ⟨hVD, ?_⟩
      intro u huV hune
      have hLu : L u ∈ V' := (Submodule.mem_inf.mp huV).1
      have hLune : L u ≠ 0 := fun h =>
        hune (hinj u (hVD huV) 0 D.zero_mem (by rw [h, map_zero]))
      rw [hform u (hVD huV)]
      exact hV'.2 (L u) hLu hLune
    have hfr : (Module.finrank ℂ V' : ℕ∞) = Module.finrank ℂ V := by
      rw [(mapEquiv L hinj hVD).finrank_eq, hmapV]
    rw [hfr]
    exact le_iSup_of_le V (le_iSup_of_le hneg (le_iSup_of_le ‹_› le_rfl))

/-! ### The embeddings land in their blocks -/

/-- `ι_tan w ∈ Dtan α` (the eigenvalue condition packaged as block membership). -/
lemma iotaTan_mem_Dtan (α : ℝ) (hα : (1 : ℝ) + Real.cos (α * Real.pi) ≠ 0)
    {w : ℤ → ℂ} (hw : MemDom w) : iotaTan α w ∈ Dtan α := by
  have hmem : iotaTan α w ∈ Domς := iotaTan_mem_Domς α hw
  refine ⟨hmem, ?_⟩
  exact rop_eq_neg_of_mulA_eq_parity α (sectorL2_of_mem_Domς hmem)
    (mulA_iotaTan α hα (CircleQ.summable_normSq hw.1))

/-- `ι_cot w ∈ Dcot α`. -/
lemma iotaCot_mem_Dcot (α : ℝ) (hα : (1 : ℝ) - Real.cos (α * Real.pi) ≠ 0)
    {w : ℤ → ℂ} (hw : MemDom w) : iotaCot α w ∈ Dcot α := by
  have hmem : iotaCot α w ∈ Domς := iotaCot_mem_Domς α hw
  refine ⟨hmem, ?_⟩
  exact rop_eq_self_of_mulA_eq_neg_parity α (sectorL2_of_mem_Domς hmem)
    (mulA_iotaCot α hα (CircleQ.summable_normSq hw.1))

/-! ### The block index equals the circle index -/

/-- **The `tan` block carries the circle index** ([ksindexi] `iop-qop_equiv`,
`+` case): `ind(𝓝_α on Dtan α) = Statements.ind (coefT α)`.  Transport along
`restrictL : Dtan α ≃ Dom` (carrying `𝓝_α ↦ 2·Q_{tan}`), then drop the factor
`2` (`formIndex_smul_pos`) and read off the circle index. -/
theorem formIndex_NQform_Dtan (α : ℝ) (hα : (1 : ℝ) + Real.cos (α * Real.pi) ≠ 0) :
    formIndex (NQform α) (Dtan α) = Statements.ind (coefT α) := by
  have htr : formIndex (NQform α) (Dtan α)
      = formIndex (fun w => 2 * Qform (coefT α) w) Dom := by
    refine formIndex_transport restrictLₗ (fun u hu => ?_) (fun u hu v hv huv => ?_)
      (fun w hw => ?_) (fun u hu => ?_)
    · exact Statements.mem_Dom.mpr (restrictL_memDom hu.1)
    · have hru := iotaTan_reconstruct α hα
        (mulA_eq_parity_of_rop_eq_neg α (sectorL2_of_mem_Domς hu.1) hu.2)
      have hrv := iotaTan_reconstruct α hα
        (mulA_eq_parity_of_rop_eq_neg α (sectorL2_of_mem_Domς hv.1) hv.2)
      simp only [restrictLₗ_apply] at huv
      rw [hru, hrv, huv]
    · exact ⟨iotaTan α w, iotaTan_mem_Dtan α hα (Statements.mem_Dom.mp hw),
        restrictL_iotaTan α w⟩
    · have hrec := iotaTan_reconstruct α hα
        (mulA_eq_parity_of_rop_eq_neg α (sectorL2_of_mem_Domς hu.1) hu.2)
      have hsum : Summable fun n : ℤ => ‖restrictL u n‖ ^ 2 :=
        CircleQ.summable_normSq (restrictL_memDom hu.1).1
      calc NQform α u = NQform α (iotaTan α (restrictL u)) := by rw [← hrec]
        _ = 2 * Qform (coefT α) (restrictL u) := NQform_iotaTan α hα hsum
        _ = 2 * Qform (coefT α) (restrictLₗ u) := by rw [restrictLₗ_apply]
  rw [htr, formIndex_smul_pos (by norm_num : (0 : ℝ) < 2), ← ind_eq_formIndex]

/-- **The `cot` block carries the circle index** ([ksindexi] `iop-qop_equiv`,
`−` case): `ind(𝓝_α on Dcot α) = Statements.ind (coefC α)`.  Mirror of
`formIndex_NQform_Dtan`. -/
theorem formIndex_NQform_Dcot (α : ℝ) (hα : (1 : ℝ) - Real.cos (α * Real.pi) ≠ 0) :
    formIndex (NQform α) (Dcot α) = Statements.ind (coefC α) := by
  have htr : formIndex (NQform α) (Dcot α)
      = formIndex (fun w => 2 * Qform (coefC α) w) Dom := by
    refine formIndex_transport restrictLₗ (fun u hu => ?_) (fun u hu v hv huv => ?_)
      (fun w hw => ?_) (fun u hu => ?_)
    · exact Statements.mem_Dom.mpr (restrictL_memDom hu.1)
    · have hru := iotaCot_reconstruct α hα
        (mulA_eq_neg_parity_of_rop_eq_self α (sectorL2_of_mem_Domς hu.1) hu.2)
      have hrv := iotaCot_reconstruct α hα
        (mulA_eq_neg_parity_of_rop_eq_self α (sectorL2_of_mem_Domς hv.1) hv.2)
      simp only [restrictLₗ_apply] at huv
      rw [hru, hrv, huv]
    · exact ⟨iotaCot α w, iotaCot_mem_Dcot α hα (Statements.mem_Dom.mp hw),
        restrictL_iotaCot α w⟩
    · have hrec := iotaCot_reconstruct α hα
        (mulA_eq_neg_parity_of_rop_eq_self α (sectorL2_of_mem_Domς hu.1) hu.2)
      have hsum : Summable fun n : ℤ => ‖restrictL u n‖ ^ 2 :=
        CircleQ.summable_normSq (restrictL_memDom hu.1).1
      calc NQform α u = NQform α (iotaCot α (restrictL u)) := by rw [← hrec]
        _ = 2 * Qform (coefC α) (restrictL u) := NQform_iotaCot α hα hsum
        _ = 2 * Qform (coefC α) (restrictLₗ u) := by rw [restrictLₗ_apply]
  rw [htr, formIndex_smul_pos (by norm_num : (0 : ℝ) < 2), ← ind_eq_formIndex]

/-! ### Block additivity of the index — the superadditive (`≥`) half

The two eigenspaces are disjoint and `𝓝_α` is block-diagonal across them
(`NQform_add_block`), so the direct sum of a `tan`-block negative subspace and a
`cot`-block negative subspace is itself `𝓝_α`-negative — giving
`ind(Dtan) + ind(Dcot) ≤ ind(Domς)`. -/

/-- The two `R_α`-eigenspaces meet only at `0` (different eigenvalues). -/
lemma Dtan_inf_Dcot (α : ℝ) : Dtan α ⊓ Dcot α = ⊥ := by
  rw [eq_bot_iff]
  intro u hu
  obtain ⟨⟨_, h1⟩, _, h2⟩ := hu
  rw [Submodule.mem_bot]
  have hself : -u = u := by rw [← h1, h2]
  have h2u : (2 : ℂ) • u = 0 := by
    rw [two_smul]
    calc u + u = -u + u := by rw [hself]
      _ = 0 := neg_add_cancel u
  rcases smul_eq_zero.mp h2u with h | h
  · norm_num at h
  · exact h

/-- **Superadditivity of the sector index**: `ind(Dtan α) + ind(Dcot α) ≤
ind(Domς)`.  A `tan`-block negative `V₁` and a `cot`-block negative `V₂` sum to a
`𝓝_α`-negative subspace of `Domς` (disjoint, block-diagonal energy), of
dimension `finrank V₁ + finrank V₂`. -/
theorem formIndex_Dtan_add_Dcot_le (α : ℝ) :
    formIndex (NQform α) (Dtan α) + formIndex (NQform α) (Dcot α)
      ≤ formIndex (NQform α) Domς := by
  rw [formIndex_eq_biSup (NQform α) (Dtan α), formIndex_eq_biSup (NQform α) (Dcot α)]
  refine ENat.biSup_add_biSup_le'
    ⟨⊥, ⟨bot_le, fun u hu h => absurd ((Submodule.mem_bot ℂ).mp hu) h⟩, inferInstance⟩
    ⟨⊥, ⟨bot_le, fun u hu h => absurd ((Submodule.mem_bot ℂ).mp hu) h⟩, inferInstance⟩ ?_
  rintro V₁ ⟨hV₁, hfd₁⟩ V₂ ⟨hV₂, hfd₂⟩
  have := hfd₁; have := hfd₂
  -- disjointness of the two negative subspaces
  have hdisj : V₁ ⊓ V₂ = ⊥ :=
    le_antisymm (le_trans (inf_le_inf hV₁.1 hV₂.1) (le_of_eq (Dtan_inf_Dcot α))) bot_le
  -- the sum is 𝓝_α-negative in Domς
  have hneg : NegOn (NQform α) Domς (V₁ ⊔ V₂) := by
    refine ⟨sup_le (le_trans hV₁.1 (Dtan_le_Domς α)) (le_trans hV₂.1 (Dcot_le_Domς α)), ?_⟩
    intro u hu hune
    obtain ⟨u₁, hu₁, u₂, hu₂, rfl⟩ := Submodule.mem_sup.mp hu
    have hd₁ : u₁ ∈ Dtan α := hV₁.1 hu₁
    have hd₂ : u₂ ∈ Dcot α := hV₂.1 hu₂
    have hblk : NQform α (u₁ + u₂) = NQform α u₁ + NQform α u₂ :=
      NQform_add_block α (mem_Domς.mp hd₁.1) (mem_Domς.mp hd₂.1) hd₁.2 hd₂.2
    rw [hblk]
    have hle₁ : NQform α u₁ ≤ 0 := by
      rcases eq_or_ne u₁ 0 with rfl | hne
      · rw [NQform_zero]
      · exact le_of_lt (hV₁.2 u₁ hu₁ hne)
    have hle₂ : NQform α u₂ ≤ 0 := by
      rcases eq_or_ne u₂ 0 with rfl | hne
      · rw [NQform_zero]
      · exact le_of_lt (hV₂.2 u₂ hu₂ hne)
    rcases eq_or_ne u₁ 0 with rfl | hne₁
    · have hu₂ne : u₂ ≠ 0 := by simpa using hune
      have : NQform α u₂ < 0 := hV₂.2 u₂ hu₂ hu₂ne
      rw [NQform_zero]; linarith
    · have : NQform α u₁ < 0 := hV₁.2 u₁ hu₁ hne₁
      linarith
  have hfr : Module.finrank ℂ (V₁ ⊔ V₂ : Submodule ℂ (Idx → ℂ))
      = Module.finrank ℂ V₁ + Module.finrank ℂ V₂ := by
    have h := Submodule.finrank_sup_add_finrank_inf_eq V₁ V₂
    rw [hdisj, finrank_bot, add_zero] at h
    exact h
  have : FiniteDimensional ℂ (V₁ ⊔ V₂ : Submodule ℂ (Idx → ℂ)) :=
    Submodule.finiteDimensional_sup V₁ V₂
  calc (Module.finrank ℂ V₁ : ℕ∞) + Module.finrank ℂ V₂
      = Module.finrank ℂ (V₁ ⊔ V₂ : Submodule ℂ (Idx → ℂ)) := by rw [hfr]; push_cast; ring
    _ ≤ formIndex (NQform α) Domς :=
        le_iSup_of_le (V₁ ⊔ V₂) (le_iSup_of_le hneg (le_iSup_of_le ‹_› le_rfl))

/-! ### Block subadditivity — the rank-≤1 (★)

The `≤` direction rests on the atomic (★): in a block of index `≤ 1` a single
negative direction `n` exhausts the negativity, so anything `B`-orthogonal to `n`
has nonnegative energy.  The mechanism is that a second `B`-orthogonal negative
vector `w` would make `span{n,w}` a 2-dimensional negative subspace. -/

/-- Energy of a linear combination of two `𝓝_α`-orthogonal vectors (in any
subblock `D ≤ Domς`): the cross terms vanish, so it is the diagonal sum
`‖s‖²·𝓝_α(n) + ‖t‖²·𝓝_α(w)`. -/
lemma NQform_span_pair (α : ℝ) {D : Submodule ℂ (Idx → ℂ)} (hDsub : D ≤ Domς)
    {n w : Idx → ℂ} (hn : n ∈ D) (hw : w ∈ D) (hBnw : NBform α n w = 0) (s t : ℂ) :
    NQform α (s • n + t • w) = ‖s‖ ^ 2 * NQform α n + ‖t‖ ^ 2 * NQform α w := by
  have hMn : MemSectorς n := mem_Domς.mp (hDsub hn)
  have hMw : MemSectorς w := mem_Domς.mp (hDsub hw)
  have hMsn : MemSectorς (s • n) := memSectorς_smul s hMn
  have hMtw : MemSectorς (t • w) := memSectorς_smul t hMw
  have hwn : NBform α w n = 0 := by rw [NBform_conj_symm, hBnw, map_zero]
  have hss : (starRingEnd ℂ) s * s = (‖s‖ : ℂ) ^ 2 := by
    rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq]; push_cast; ring
  have htt : (starRingEnd ℂ) t * t = (‖t‖ : ℂ) ^ 2 := by
    rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq]; push_cast; ring
  have hcast : (NQform α (s • n + t • w) : ℂ)
      = ((‖s‖ ^ 2 * NQform α n + ‖t‖ ^ 2 * NQform α w : ℝ) : ℂ) := by
    rw [← NBform_self, NBform_add_left α hMsn hMtw (memSectorς_add hMsn hMtw),
      NBform_add_right α hMsn hMsn hMtw, NBform_add_right α hMtw hMsn hMtw,
      NBform_smul_left, NBform_smul_left, NBform_smul_left, NBform_smul_left,
      NBform_smul_right, NBform_smul_right, NBform_smul_right, NBform_smul_right,
      NBform_self α n, NBform_self α w, hBnw, hwn]
    push_cast
    linear_combination (NQform α n : ℂ) * hss + (NQform α w : ℂ) * htt
  exact_mod_cast hcast

/-- **The atomic (★)**: in a subblock `D ≤ Domς` of index `≤ 1`, a single
negative direction `n` exhausts the negativity — every `w ∈ D` that is
`𝓝_α`-orthogonal to `n` has `𝓝_α(w) ≥ 0`.  (Else `span{n,w}` is a
2-dimensional `𝓝_α`-negative subspace, forcing index `≥ 2`.) -/
theorem nonneg_of_orthogonal (α : ℝ) {D : Submodule ℂ (Idx → ℂ)} (hDsub : D ≤ Domς)
    (hind : formIndex (NQform α) D ≤ 1)
    {n : Idx → ℂ} (hn : n ∈ D) (hQn : NQform α n < 0)
    {w : Idx → ℂ} (hw : w ∈ D) (hBnw : NBform α n w = 0) :
    0 ≤ NQform α w := by
  by_contra hlt
  rw [not_le] at hlt
  -- `n`, `w` are linearly independent (else `B n w ≠ 0`)
  have hindep : LinearIndependent ℂ ![n, w] := by
    rw [LinearIndependent.pair_iff]
    intro s t hst
    have hMn : MemSectorς n := mem_Domς.mp (hDsub hn)
    have hMw : MemSectorς w := mem_Domς.mp (hDsub hw)
    have hsn : (NQform α n : ℂ) ≠ 0 := by exact_mod_cast ne_of_lt hQn
    have hzero : NBform α n (s • n + t • w) = 0 := by
      rw [hst]; simpa using NBform_smul_right α 0 n n
    rw [NBform_add_right α hMn (memSectorς_smul s hMn) (memSectorς_smul t hMw),
      NBform_smul_right, NBform_smul_right, NBform_self α n, hBnw, mul_zero,
      add_zero] at hzero
    -- hzero : s * (NQform α n : ℂ) = 0
    have hs0 : s = 0 := by
      rcases mul_eq_zero.mp hzero with h | h
      · exact h
      · exact absurd h hsn
    refine ⟨hs0, ?_⟩
    rw [hs0, zero_smul, zero_add] at hst
    have hwne : w ≠ 0 := fun h => by rw [h, NQform_zero] at hlt; exact lt_irrefl _ hlt
    rcases smul_eq_zero.mp hst with h | h
    · exact h
    · exact absurd h hwne
  -- `span{n,w}` is a 2-dim negative subspace ⟹ formIndex ≥ 2
  set S := Submodule.span ℂ (Set.range ![n, w]) with hS
  have hrange : (Set.range ![n, w]) = {n, w} := by
    ext x
    simp only [Set.mem_range, Fin.exists_fin_two, Matrix.cons_val_zero, Matrix.cons_val_one,
      Set.mem_insert_iff, Set.mem_singleton_iff]
    tauto
  have hfr : Module.finrank ℂ S = 2 := by
    rw [hS, finrank_span_eq_card hindep]; simp
  haveI : FiniteDimensional ℂ S := by
    rw [hS]; exact FiniteDimensional.span_of_finite _ (Set.finite_range _)
  have hSle : S ≤ D := by
    rw [hS, Submodule.span_le, hrange]
    intro x hx
    rcases hx with rfl | rfl <;> [exact hn; exact hw]
  have hSneg : NegOn (NQform α) D S := by
    refine ⟨hSle, ?_⟩
    intro u hu hune
    rw [hS, hrange, Submodule.mem_span_pair] at hu
    obtain ⟨s, t, rfl⟩ := hu
    rw [NQform_span_pair α hDsub hn hw hBnw]
    have hst : ¬ (s = 0 ∧ t = 0) := by
      rintro ⟨rfl, rfl⟩; simp at hune
    have hs2 : (0 : ℝ) ≤ ‖s‖ ^ 2 := sq_nonneg _
    have ht2 : (0 : ℝ) ≤ ‖t‖ ^ 2 := sq_nonneg _
    rcases eq_or_ne s 0 with rfl | hsne
    · have htne : t ≠ 0 := fun h => hst ⟨rfl, h⟩
      have : (0 : ℝ) < ‖t‖ ^ 2 := by positivity
      have h1 : ‖(0:ℂ)‖ ^ 2 * NQform α n = 0 := by simp
      rw [h1, zero_add]; nlinarith [mul_neg_of_pos_of_neg this hlt]
    · have : (0 : ℝ) < ‖s‖ ^ 2 := by positivity
      nlinarith [mul_neg_of_pos_of_neg this hQn, mul_nonpos_of_nonneg_of_nonpos ht2 (le_of_lt hlt)]
  have h2 : (2 : ℕ∞) ≤ formIndex (NQform α) D := by
    have hle : (Module.finrank ℂ S : ℕ∞) ≤ formIndex (NQform α) D :=
      le_iSup_of_le S (le_iSup_of_le hSneg (le_iSup_of_le ‹_› le_rfl))
    rw [hfr] at hle
    exact_mod_cast hle
  exact absurd (le_trans h2 hind) (by decide)

/-- **Eigenprojection decomposition**: every domain vector splits into its
`tan`-block and `cot`-block parts, `w = (I−R_α)/2·w + (I+R_α)/2·w`. -/
lemma exists_eigen_decomp (α : ℝ) {w : Idx → ℂ} (hw : w ∈ Domς) :
    ∃ wt ∈ Dtan α, ∃ wc ∈ Dcot α, w = wt + wc := by
  have hSw : SectorL2 w := sectorL2_of_mem_Domς hw
  have hrw : rop α w ∈ Domς := rop_mem_Domς α hw
  have hSrw : SectorL2 (rop α w) := sectorL2_of_mem_Domς hrw
  refine ⟨(2⁻¹ : ℂ) • (w - rop α w),
      ⟨Submodule.smul_mem _ _ (Submodule.sub_mem _ hw hrw), ?_⟩,
    (2⁻¹ : ℂ) • (w + rop α w),
      ⟨Submodule.smul_mem _ _ (Submodule.add_mem _ hw hrw), ?_⟩, ?_⟩
  · rw [rop_smul, rop_sub α hSw hSrw, rop_involutive α hSw, smul_sub, smul_sub]; abel
  · rw [rop_smul, rop_add α hSw hSrw, rop_involutive α hSw, add_comm (rop α w) w]
  · module

/-! ### Index ↔ negativity bridges for `𝓝_α`

Two elementary facts about `formIndex (NQform α)` that the `≤`-direction assembly
needs: a single `𝓝_α`-negative vector forces index `≥ 1` (`one_le_formIndex_of_neg`),
and conversely index `0` means `𝓝_α ≥ 0` on the whole block (`nonneg_of_index_zero`);
`exists_neg_of_one_le` extracts a negative direction from an index-`≥ 1` block. -/

/-- Homogeneity of the `𝓝_α`-energy: `𝓝_α(c·u) = ‖c‖²·𝓝_α(u)` (unconditional,
from the sesquilinear scaling of `NBform`). -/
lemma NQform_smul (α : ℝ) (c : ℂ) (u : Idx → ℂ) :
    NQform α (c • u) = ‖c‖ ^ 2 * NQform α u := by
  have hcc : (starRingEnd ℂ) c * c = (‖c‖ : ℂ) ^ 2 := by
    rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq]; push_cast; ring
  have hcast : (NQform α (c • u) : ℂ) = ((‖c‖ ^ 2 * NQform α u : ℝ) : ℂ) := by
    rw [← NBform_self, NBform_smul_left, NBform_smul_right, NBform_self]
    push_cast
    linear_combination (NQform α u : ℂ) * hcc
  exact_mod_cast hcast

/-- A single `𝓝_α`-negative direction forces index `≥ 1`. -/
lemma one_le_formIndex_of_neg (α : ℝ) {D : Submodule ℂ (Idx → ℂ)}
    {n : Idx → ℂ} (hn : n ∈ D) (hneg : NQform α n < 0) :
    1 ≤ formIndex (NQform α) D := by
  have hn0 : n ≠ 0 := fun h => by rw [h, NQform_zero] at hneg; exact lt_irrefl _ hneg
  set S := Submodule.span ℂ {n} with hS
  have hSle : S ≤ D := by
    rw [hS, Submodule.span_le, Set.singleton_subset_iff]; exact hn
  have hfr : Module.finrank ℂ S = 1 := by rw [hS, finrank_span_singleton hn0]
  have : FiniteDimensional ℂ S := by
    rw [hS]; exact FiniteDimensional.span_of_finite _ (Set.finite_singleton n)
  have hSneg : NegOn (NQform α) D S := by
    refine ⟨hSle, ?_⟩
    intro u hu hune
    rw [hS, Submodule.mem_span_singleton] at hu
    obtain ⟨c, rfl⟩ := hu
    rw [NQform_smul]
    have hc0 : c ≠ 0 := fun h => hune (by rw [h, zero_smul])
    have : (0 : ℝ) < ‖c‖ ^ 2 := by positivity
    exact mul_neg_of_pos_of_neg this hneg
  have hle : (Module.finrank ℂ S : ℕ∞) ≤ formIndex (NQform α) D :=
    le_iSup_of_le S (le_iSup_of_le hSneg (le_iSup_of_le ‹_› le_rfl))
  rw [hfr] at hle
  exact_mod_cast hle

/-- Index `0` block: `𝓝_α ≥ 0` everywhere on it. -/
lemma nonneg_of_index_zero (α : ℝ) {D : Submodule ℂ (Idx → ℂ)}
    (h0 : formIndex (NQform α) D = 0) {w : Idx → ℂ} (hw : w ∈ D) :
    0 ≤ NQform α w := by
  by_contra hlt
  rw [not_le] at hlt
  have h1 := one_le_formIndex_of_neg α hw hlt
  rw [h0] at h1
  exact absurd h1 (by decide)

/-- Extract a `𝓝_α`-negative direction from an index-`≥ 1` block. -/
lemma exists_neg_of_one_le (α : ℝ) {D : Submodule ℂ (Idx → ℂ)}
    (h1 : 1 ≤ formIndex (NQform α) D) : ∃ n ∈ D, NQform α n < 0 := by
  by_contra h
  simp only [not_exists, not_and, not_lt] at h
  have hle0 : formIndex (NQform α) D ≤ 0 := by
    refine iSup_le fun V => iSup_le fun hV => iSup_le fun hfd => ?_
    have := hfd
    have hbot : V = ⊥ := by
      rw [eq_bot_iff]
      intro v hv
      rw [Submodule.mem_bot]
      by_contra hvne
      have hn := hV.2 v hv hvne
      have hp := h v (hV.1 hv)
      linarith
    rw [hbot, finrank_bot]; simp
  exact absurd (le_trans h1 hle0) (by decide)

/-! ### The per-block B-orthogonal projection (`block_data`)

For each `R_α`-block `D ≤ Domς` of index `≤ 1`, `block_data` packages a maximal
`𝓝_α`-negative submodule `N ≤ D` (`finrank N = index`) together with a bundled
linear projection `φ : ↥Domς →ₗ[ℂ] (Idx→ℂ)` onto `N` that (i) vanishes on the
complementary block `Do`, and (ii) satisfies the atomic (★): if `φ v = 0` and
`v ∈ D` then `𝓝_α(v) ≥ 0`.  Two cases: index `0` (take `N = ⊥`, `φ = 0`,
guarantee from `nonneg_of_index_zero`) and index `1` (`N = span{n}` for an
extracted negative `n`, `φ v = (𝓝_α(n)⁻¹·𝓝_α(n,v))·n` the B-orthogonal
projection, guarantee from `nonneg_of_orthogonal`).  The combination assembles the
two blocks' projections into an injective map bounding `finrank` by the sum. -/
theorem block_data (α : ℝ) {D Do : Submodule ℂ (Idx → ℂ)} (hDsub : D ≤ Domς)
    (hind : formIndex (NQform α) D ≤ 1)
    (horth : ∀ n ∈ D, ∀ v ∈ Do, NBform α n v = 0) :
    ∃ (N : Submodule ℂ (Idx → ℂ)) (φ : ↥Domς →ₗ[ℂ] (Idx → ℂ)),
      (Module.finrank ℂ N : ℕ∞) = formIndex (NQform α) D ∧
      FiniteDimensional ℂ N ∧
      (∀ v : ↥Domς, φ v ∈ N) ∧
      (∀ v : ↥Domς, (v : Idx → ℂ) ∈ Do → φ v = 0) ∧
      (∀ v : ↥Domς, (v : Idx → ℂ) ∈ D → φ v = 0 → 0 ≤ NQform α (v : Idx → ℂ)) := by
  rcases eq_or_ne (formIndex (NQform α) D) 0 with h0 | hne
  · -- index 0: N = ⊥, φ = 0
    refine ⟨⊥, 0, ?_, inferInstance, ?_, ?_, ?_⟩
    · rw [finrank_bot, h0]; rfl
    · intro v; simp
    · intro v _; rfl
    · intro v hvD _; exact nonneg_of_index_zero α h0 hvD
  · -- index 1: extract negative n, N = span{n}
    have h1le : (1 : ℕ∞) ≤ formIndex (NQform α) D := Order.one_le_iff_ne_zero.mpr hne
    obtain ⟨n, hnD, hnneg⟩ := exists_neg_of_one_le α h1le
    have hnMem : MemSectorς n := mem_Domς.mp (hDsub hnD)
    have hn0 : n ≠ 0 := fun h => by rw [h, NQform_zero] at hnneg; exact lt_irrefl _ hnneg
    have hc0 : (NQform α n : ℂ) ≠ 0 := by exact_mod_cast ne_of_lt hnneg
    set c : ℂ := (NQform α n : ℂ) with hc
    -- the bundled B-orthogonal projection φ v = (c⁻¹ · 𝓝_α(n, v)) · n
    refine ⟨Submodule.span ℂ {n},
      { toFun := fun v => (c⁻¹ * NBform α n (v : Idx → ℂ)) • n
        map_add' := fun v w => by
          have hv := mem_Domς.mp v.2
          have hw := mem_Domς.mp w.2
          simp only [Submodule.coe_add]
          rw [NBform_add_right α hnMem hv hw, mul_add, add_smul]
        map_smul' := fun c' v => by
          simp only [Submodule.coe_smul, RingHom.id_apply]
          rw [NBform_smul_right, smul_smul]
          congr 1
          ring },
      ?_, ?_, ?_, ?_, ?_⟩
    · -- finrank = index = 1
      have hfeq : formIndex (NQform α) D = 1 := le_antisymm hind h1le
      rw [finrank_span_singleton hn0, hfeq]; rfl
    · exact FiniteDimensional.span_of_finite _ (Set.finite_singleton n)
    · -- range in span{n}
      intro v
      exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self n)
    · -- vanishes on Do
      intro v hvDo
      have hz : NBform α n (v : Idx → ℂ) = 0 := horth n hnD (v : Idx → ℂ) hvDo
      change (c⁻¹ * NBform α n (v : Idx → ℂ)) • n = 0
      rw [hz, mul_zero, zero_smul]
    · -- the guarantee (★)
      intro v hvD hφ0
      have hφ0' : (c⁻¹ * NBform α n (v : Idx → ℂ)) • n = 0 := hφ0
      have hscal : c⁻¹ * NBform α n (v : Idx → ℂ) = 0 := by
        by_contra hsc
        exact hn0 ((smul_eq_zero.mp hφ0').resolve_left hsc)
      have hBz : NBform α n (v : Idx → ℂ) = 0 := by
        rcases mul_eq_zero.mp hscal with h | h
        · exact absurd (inv_eq_zero.mp h) hc0
        · exact h
      exact nonneg_of_orthogonal α hDsub hind hnD hnneg hvD hBz

/-! ### Block subadditivity — the `≤` half

Assembling the two blocks' B-orthogonal projections (`block_data`) into a single
map `↥V →ₗ ↥Nt × ↥Nc` for any `𝓝_α`-negative `V ≤ Domς`.  The map is injective:
if it kills `x`, then `x`'s `tan`- and `cot`-parts are each `B`-orthogonal to
their block's negative direction, hence (★) nonnegative, so `𝓝_α(x) ≥ 0` — but
`x ≠ 0` in the negative subspace `V` forces `𝓝_α(x) < 0`.  Injectivity gives
`finrank V ≤ finrank Nt + finrank Nc = ind(Dtan) + ind(Dcot)`. -/
theorem formIndex_Domς_le_add (α : ℝ)
    (hindtan : formIndex (NQform α) (Dtan α) ≤ 1)
    (hindcot : formIndex (NQform α) (Dcot α) ≤ 1) :
    formIndex (NQform α) Domς
      ≤ formIndex (NQform α) (Dtan α) + formIndex (NQform α) (Dcot α) := by
  -- cross B-orthogonality of the two eigenblocks
  have horth_tan : ∀ n ∈ Dtan α, ∀ v ∈ Dcot α, NBform α n v = 0 := by
    intro n hn v hv
    exact NBform_eigen_orthogonal α (sectorL2_of_mem_Domς hn.1) (sectorL2_of_mem_Domς hv.1)
      hn.2 hv.2
  have horth_cot : ∀ n ∈ Dcot α, ∀ v ∈ Dtan α, NBform α n v = 0 := by
    intro n hn v hv
    have h := NBform_eigen_orthogonal α (sectorL2_of_mem_Domς hv.1) (sectorL2_of_mem_Domς hn.1)
      hv.2 hn.2
    rw [NBform_conj_symm α v n, h, map_zero]
  -- per-block projection data
  obtain ⟨Nt, φt, hNtfr, hNtfd, hφtN, hφtDo, hφtG⟩ :=
    block_data α (Dtan_le_Domς α) hindtan horth_tan
  obtain ⟨Nc, φc, hNcfr, hNcfd, hφcN, hφcDo, hφcG⟩ :=
    block_data α (Dcot_le_Domς α) hindcot horth_cot
  haveI := hNtfd; haveI := hNcfd
  refine iSup_le fun V => iSup_le fun hV => iSup_le fun hfd => ?_
  have := hfd
  set emb : ↥V →ₗ[ℂ] ↥Domς := Submodule.inclusion hV.1 with hemb
  set gt : ↥V →ₗ[ℂ] ↥Nt := (φt.comp emb).codRestrict Nt (fun x => hφtN (emb x)) with hgt
  set gc : ↥V →ₗ[ℂ] ↥Nc := (φc.comp emb).codRestrict Nc (fun x => hφcN (emb x)) with hgc
  set g : ↥V →ₗ[ℂ] (↥Nt × ↥Nc) := gt.prod gc with hgdef
  have hg_inj : Function.Injective g := by
    rw [← LinearMap.ker_eq_bot, eq_bot_iff]
    intro x hx
    rw [Submodule.mem_bot]
    have h0 : g x = 0 := LinearMap.mem_ker.mp hx
    rw [hgdef, LinearMap.prod_apply, Prod.mk_eq_zero] at h0
    obtain ⟨hgtx, hgcx⟩ := h0
    have hφt0 : φt (emb x) = 0 := congrArg Subtype.val hgtx
    have hφc0 : φc (emb x) = 0 := congrArg Subtype.val hgcx
    -- decompose x's underlying vector into eigenparts
    have hw : (x : Idx → ℂ) ∈ Domς := hV.1 x.2
    obtain ⟨wt, hwt, wc, hwc, hsum⟩ := exists_eigen_decomp α hw
    set vt : ↥Domς := ⟨wt, Dtan_le_Domς α hwt⟩ with hvt
    set vc : ↥Domς := ⟨wc, Dcot_le_Domς α hwc⟩ with hvc
    have hembsum : emb x = vt + vc := by
      apply Subtype.ext
      change (x : Idx → ℂ) = wt + wc
      exact hsum
    -- tan part: φt vt = 0, so 𝓝_α(wt) ≥ 0
    have hφtvc : φt vc = 0 := hφtDo vc hwc
    have hφtvt : φt vt = 0 := by
      have hexp : φt (emb x) = φt vt + φt vc := by rw [hembsum, map_add]
      rw [hφt0, hφtvc, add_zero] at hexp
      exact hexp.symm
    have hQwt : 0 ≤ NQform α wt := hφtG vt hwt hφtvt
    -- cot part: φc vc = 0, so 𝓝_α(wc) ≥ 0
    have hφcvt : φc vt = 0 := hφcDo vt hwt
    have hφcvc : φc vc = 0 := by
      have hexp : φc (emb x) = φc vt + φc vc := by rw [hembsum, map_add]
      rw [hφc0, hφcvt, zero_add] at hexp
      exact hexp.symm
    have hQwc : 0 ≤ NQform α wc := hφcG vc hwc hφcvc
    -- block-diagonal energy is ≥ 0, contradicting V-negativity
    have hwt_mem : MemSectorς wt := mem_Domς.mp (Dtan_le_Domς α hwt)
    have hwc_mem : MemSectorς wc := mem_Domς.mp (Dcot_le_Domς α hwc)
    have hQge : 0 ≤ NQform α (x : Idx → ℂ) := by
      rw [hsum, NQform_add_block α hwt_mem hwc_mem hwt.2 hwc.2]
      linarith
    by_contra hxne
    have hxv : (x : Idx → ℂ) ≠ 0 := fun h => hxne (Subtype.ext h)
    have hlt := hV.2 (x : Idx → ℂ) x.2 hxv
    linarith
  -- injectivity ⟹ finrank bound
  have hfin : Module.finrank ℂ ↥V ≤ Module.finrank ℂ ((↥Nt) × (↥Nc)) :=
    LinearMap.finrank_le_finrank_of_injective hg_inj
  rw [Module.finrank_prod] at hfin
  calc (Module.finrank ℂ ↥V : ℕ∞)
      ≤ ((Module.finrank ℂ ↥Nt + Module.finrank ℂ ↥Nc : ℕ) : ℕ∞) := by exact_mod_cast hfin
    _ = (Module.finrank ℂ ↥Nt : ℕ∞) + (Module.finrank ℂ ↥Nc : ℕ∞) := by push_cast; ring
    _ = formIndex (NQform α) (Dtan α) + formIndex (NQform α) (Dcot α) := by
        rw [hNtfr, hNcfr]

/-! ### The `iop-qop` index identity

Combining superadditivity (`formIndex_Dtan_add_Dcot_le`) with subadditivity
(`formIndex_Domς_le_add`) and the block-index-equals-circle-index transports
gives the paper's `iop-qop_equiv` at the level of the Morse index:

    ind(𝓝_{3,α}) = ind(𝒬_{tan(απ/2)}) + ind(𝒬_{cot(απ/2)}). -/
theorem formIndex_NQform_Domς (α : ℝ)
    (hαT : (1 : ℝ) + Real.cos (α * Real.pi) ≠ 0)
    (hαC : (1 : ℝ) - Real.cos (α * Real.pi) ≠ 0) :
    formIndex (NQform α) Domς = Statements.ind (coefT α) + Statements.ind (coefC α) := by
  have hindtan : formIndex (NQform α) (Dtan α) ≤ 1 := by
    rw [formIndex_NQform_Dtan α hαT]
    exact le_trans le_self_add (Statements.ind_add_nul_le_one (coefT α))
  have hindcot : formIndex (NQform α) (Dcot α) ≤ 1 := by
    rw [formIndex_NQform_Dcot α hαC]
    exact le_trans le_self_add (Statements.ind_add_nul_le_one (coefC α))
  refine le_antisymm ?_ ?_
  · calc formIndex (NQform α) Domς
        ≤ formIndex (NQform α) (Dtan α) + formIndex (NQform α) (Dcot α) :=
          formIndex_Domς_le_add α hindtan hindcot
      _ = Statements.ind (coefT α) + Statements.ind (coefC α) := by
          rw [formIndex_NQform_Dtan α hαT, formIndex_NQform_Dcot α hαC]
  · calc Statements.ind (coefT α) + Statements.ind (coefC α)
        = formIndex (NQform α) (Dtan α) + formIndex (NQform α) (Dcot α) := by
          rw [formIndex_NQform_Dtan α hαT, formIndex_NQform_Dcot α hαC]
      _ ≤ formIndex (NQform α) Domς := formIndex_Dtan_add_Dcot_le α

/-! ### The bilinear iota correspondence

The nullity mirror needs the *polarized* form of `NQform_iotaTan`: the sector
form pairs two embedded circle vectors as twice the circle `Bform`.  The `mulA`
term reduces to a `bN3`-parity via `mulA_iotaTan`, and `bN3` of two embedded
vectors is the circle `Bform` at `s = coefT α` (the `inr`-coefficient `i·coefT`
contributes `conj(i·coefT)·(i·coefT) = coefT²`, exactly the `s²` weight). -/

/-- `bN3 (ι_tan w) (ι_tan w') = Bform (coefT α) w w'`: the base `N₃`-pairing of
two `tan`-embedded vectors is the circle polarization.  The `inl` half matches
the `+`-lattice term verbatim; the `inr` half contributes the factor
`conj(i·coefT)·(i·coefT) = coefT²` = the `s²` weight of `Bform`. -/
lemma bN3_iotaTan_eq_Bform (α : ℝ) (w w' : ℤ → ℂ) :
    bN3 (iotaTan α w) (iotaTan α w') = Bform (coefT α) w w' := by
  have hI : Complex.I * Complex.I = -1 := Complex.I_mul_I
  rw [bN3, Bform]
  refine congr_arg₂ (· + ·) rfl ?_
  rw [← tsum_mul_left]
  refine tsum_congr fun m => ?_
  rw [iotaTan_inr, iotaTan_inr]
  simp only [map_mul, Complex.conj_I, Complex.conj_ofReal]
  linear_combination
    (-(sigM m : ℂ) * (coefT α : ℂ) ^ 2 * (starRingEnd ℂ) (convS w m) * convS w' m) * hI

/-- **`𝓝_α(ι_tan w, ι_tan w') = 2·Bform (coefT α) w w'`** — the polarized
`iop-qop_equiv` item 2 (`+` case).  On `ker(R_α + I)`, `M_α = P`, so the second
`bN3` term doubles the first (`bN3_parity`). -/
lemma NBform_iotaTan (α : ℝ) (hα : (1 : ℝ) + Real.cos (α * Real.pi) ≠ 0)
    {w w' : ℤ → ℂ} (hw : Summable fun n : ℤ => ‖w n‖ ^ 2)
    (hw' : Summable fun n : ℤ => ‖w' n‖ ^ 2) :
    NBform α (iotaTan α w) (iotaTan α w') = 2 * Bform (coefT α) w w' := by
  rw [NBform, mulA_iotaTan α hα hw, mulA_iotaTan α hα hw', bN3_parity,
    bN3_iotaTan_eq_Bform]
  ring

/-- `bN3 (ι_cot w) (ι_cot w') = Bform (coefC α) w w'` — the `cot` mirror. -/
lemma bN3_iotaCot_eq_Bform (α : ℝ) (w w' : ℤ → ℂ) :
    bN3 (iotaCot α w) (iotaCot α w') = Bform (coefC α) w w' := by
  have hI : Complex.I * Complex.I = -1 := Complex.I_mul_I
  rw [bN3, Bform]
  refine congr_arg₂ (· + ·) rfl ?_
  rw [← tsum_mul_left]
  refine tsum_congr fun m => ?_
  rw [iotaCot_inr, iotaCot_inr]
  simp only [map_mul, Complex.conj_I, Complex.conj_ofReal]
  linear_combination
    (-(sigM m : ℂ) * (coefC α : ℂ) ^ 2 * (starRingEnd ℂ) (convS w m) * convS w' m) * hI

/-- **`𝓝_α(ι_cot w, ι_cot w') = 2·Bform (coefC α) w w'`** — item 2, `−` case.
On `ker(R_α − I)`, `M_α = −P`, so `bN3_neg_neg` then `bN3_parity` double it. -/
lemma NBform_iotaCot (α : ℝ) (hα : (1 : ℝ) - Real.cos (α * Real.pi) ≠ 0)
    {w w' : ℤ → ℂ} (hw : Summable fun n : ℤ => ‖w n‖ ^ 2)
    (hw' : Summable fun n : ℤ => ‖w' n‖ ^ 2) :
    NBform α (iotaCot α w) (iotaCot α w') = 2 * Bform (coefC α) w w' := by
  rw [NBform, mulA_iotaCot α hα hw, mulA_iotaCot α hα hw', bN3_neg_neg, bN3_parity,
    bN3_iotaCot_eq_Bform]
  ring

/-! ### Generic nullity transport along an injective-on-domain linear map

The bilinear counterpart of `formIndex_transport`: an injective-on-`D` linear
map `L` carrying the Hermitian form `B` on `D` to `B'` on `D'` transports the
nullity.  The radical condition ranges over *all* of the domain, so surjectivity
of `L : D ↠ D'` is used both ways (to hit every test vector). -/
theorem formNullity_transport {ι κ : Type*} (L : (ι → ℂ) →ₗ[ℂ] (κ → ℂ))
    {B : (ι → ℂ) → (ι → ℂ) → ℂ} {B' : (κ → ℂ) → (κ → ℂ) → ℂ}
    {D : Submodule ℂ (ι → ℂ)} {D' : Submodule ℂ (κ → ℂ)}
    (hmap : ∀ u ∈ D, L u ∈ D')
    (hinj : ∀ u ∈ D, ∀ v ∈ D, L u = L v → u = v)
    (hsurj : ∀ w ∈ D', ∃ u ∈ D, L u = w)
    (hform : ∀ u ∈ D, ∀ v ∈ D, B u v = B' (L u) (L v)) :
    formNullity B D = formNullity B' D' := by
  apply le_antisymm
  · refine iSup_le fun V => iSup_le fun hV => iSup_le fun hfd => ?_
    have := hfd
    have hfd' : FiniteDimensional ℂ ↥(V.map L) := Module.Finite.equiv (mapEquiv L hinj hV.1)
    have hnull : NullOn B' D' (V.map L) := by
      refine ⟨Submodule.map_le_iff_le_comap.mpr fun u hu => hmap u (hV.1 hu), ?_⟩
      intro x hx y hy
      obtain ⟨u, huV, rfl⟩ := Submodule.mem_map.mp hx
      obtain ⟨v, hvD, rfl⟩ := hsurj y hy
      rw [← hform u (hV.1 huV) v hvD]
      exact hV.2 u huV v hvD
    have hfr : (Module.finrank ℂ V : ℕ∞) = Module.finrank ℂ ↥(V.map L) := by
      rw [(mapEquiv L hinj hV.1).finrank_eq]
    rw [hfr]
    exact le_iSup_of_le (V.map L) (le_iSup_of_le hnull (le_iSup_of_le hfd' le_rfl))
  · refine iSup_le fun V' => iSup_le fun hV' => iSup_le fun hfd' => ?_
    have := hfd'
    set V := (V'.comap L) ⊓ D with hVdef
    have hVD : V ≤ D := inf_le_right
    have hmapV : V.map L = V' := by
      apply le_antisymm
      · exact Submodule.map_le_iff_le_comap.mpr fun u hu => (Submodule.mem_inf.mp hu).1
      · intro w hw
        obtain ⟨u, huD, hLuw⟩ := hsurj w (hV'.1 hw)
        refine Submodule.mem_map.mpr ⟨u, Submodule.mem_inf.mpr
          ⟨Submodule.mem_comap.mpr (by rw [hLuw]; exact hw), huD⟩, hLuw⟩
    have hfdV : FiniteDimensional ℂ ↥(V.map L) := hmapV ▸ hfd'
    have hfdV' : FiniteDimensional ℂ V := Module.Finite.equiv (mapEquiv L hinj hVD).symm
    have hnull : NullOn B D V := by
      refine ⟨hVD, ?_⟩
      intro u huV v hvD
      have hLu : L u ∈ V' := (Submodule.mem_inf.mp huV).1
      have hLv : L v ∈ D' := hmap v hvD
      rw [hform u (hVD huV) v hvD]
      exact hV'.2 (L u) hLu (L v) hLv
    have hfr : (Module.finrank ℂ V' : ℕ∞) = Module.finrank ℂ V := by
      rw [(mapEquiv L hinj hVD).finrank_eq, hmapV]
    rw [hfr]
    exact le_iSup_of_le V (le_iSup_of_le hnull (le_iSup_of_le hfdV' le_rfl))

/-! ### The block nullity equals the circle nullity -/

/-- **The `tan` block carries the circle nullity** (`iop-qop_equiv`, `+` case,
nullity level): `nul(𝓝_α on Dtan α) = Statements.nul (coefT α)`.  Transport
along `restrictL : Dtan α ≃ Dom` carrying `𝓝_α ↦ 2·B_{tan}`, then drop the
factor `2` (`formNullity_smul_ne_zero`). -/
theorem formNullity_NBform_Dtan (α : ℝ) (hα : (1 : ℝ) + Real.cos (α * Real.pi) ≠ 0) :
    formNullity (NBform α) (Dtan α) = Statements.nul (coefT α) := by
  have htr : formNullity (NBform α) (Dtan α)
      = formNullity (fun w w' => 2 * Bform (coefT α) w w') Dom := by
    refine formNullity_transport restrictLₗ (fun u hu => ?_) (fun u hu v hv huv => ?_)
      (fun w hw => ?_) (fun u hu v hv => ?_)
    · exact Statements.mem_Dom.mpr (restrictL_memDom hu.1)
    · have hru := iotaTan_reconstruct α hα
        (mulA_eq_parity_of_rop_eq_neg α (sectorL2_of_mem_Domς hu.1) hu.2)
      have hrv := iotaTan_reconstruct α hα
        (mulA_eq_parity_of_rop_eq_neg α (sectorL2_of_mem_Domς hv.1) hv.2)
      simp only [restrictLₗ_apply] at huv
      rw [hru, hrv, huv]
    · exact ⟨iotaTan α w, iotaTan_mem_Dtan α hα (Statements.mem_Dom.mp hw),
        restrictL_iotaTan α w⟩
    · have hrecu := iotaTan_reconstruct α hα
        (mulA_eq_parity_of_rop_eq_neg α (sectorL2_of_mem_Domς hu.1) hu.2)
      have hrecv := iotaTan_reconstruct α hα
        (mulA_eq_parity_of_rop_eq_neg α (sectorL2_of_mem_Domς hv.1) hv.2)
      have hsumu : Summable fun n : ℤ => ‖restrictL u n‖ ^ 2 :=
        CircleQ.summable_normSq (restrictL_memDom hu.1).1
      have hsumv : Summable fun n : ℤ => ‖restrictL v n‖ ^ 2 :=
        CircleQ.summable_normSq (restrictL_memDom hv.1).1
      calc NBform α u v
          = NBform α (iotaTan α (restrictL u)) (iotaTan α (restrictL v)) := by
            rw [← hrecu, ← hrecv]
        _ = 2 * Bform (coefT α) (restrictL u) (restrictL v) := NBform_iotaTan α hα hsumu hsumv
        _ = 2 * Bform (coefT α) (restrictLₗ u) (restrictLₗ v) := by
            rw [restrictLₗ_apply, restrictLₗ_apply]
  rw [htr, formNullity_smul_ne_zero (B := Bform (coefT α)) (by norm_num : (2 : ℂ) ≠ 0),
    ← nul_eq_formNullity]

/-- **The `cot` block carries the circle nullity** (`−` case).  Mirror of
`formNullity_NBform_Dtan`. -/
theorem formNullity_NBform_Dcot (α : ℝ) (hα : (1 : ℝ) - Real.cos (α * Real.pi) ≠ 0) :
    formNullity (NBform α) (Dcot α) = Statements.nul (coefC α) := by
  have htr : formNullity (NBform α) (Dcot α)
      = formNullity (fun w w' => 2 * Bform (coefC α) w w') Dom := by
    refine formNullity_transport restrictLₗ (fun u hu => ?_) (fun u hu v hv huv => ?_)
      (fun w hw => ?_) (fun u hu v hv => ?_)
    · exact Statements.mem_Dom.mpr (restrictL_memDom hu.1)
    · have hru := iotaCot_reconstruct α hα
        (mulA_eq_neg_parity_of_rop_eq_self α (sectorL2_of_mem_Domς hu.1) hu.2)
      have hrv := iotaCot_reconstruct α hα
        (mulA_eq_neg_parity_of_rop_eq_self α (sectorL2_of_mem_Domς hv.1) hv.2)
      simp only [restrictLₗ_apply] at huv
      rw [hru, hrv, huv]
    · exact ⟨iotaCot α w, iotaCot_mem_Dcot α hα (Statements.mem_Dom.mp hw),
        restrictL_iotaCot α w⟩
    · have hrecu := iotaCot_reconstruct α hα
        (mulA_eq_neg_parity_of_rop_eq_self α (sectorL2_of_mem_Domς hu.1) hu.2)
      have hrecv := iotaCot_reconstruct α hα
        (mulA_eq_neg_parity_of_rop_eq_self α (sectorL2_of_mem_Domς hv.1) hv.2)
      have hsumu : Summable fun n : ℤ => ‖restrictL u n‖ ^ 2 :=
        CircleQ.summable_normSq (restrictL_memDom hu.1).1
      have hsumv : Summable fun n : ℤ => ‖restrictL v n‖ ^ 2 :=
        CircleQ.summable_normSq (restrictL_memDom hv.1).1
      calc NBform α u v
          = NBform α (iotaCot α (restrictL u)) (iotaCot α (restrictL v)) := by
            rw [← hrecu, ← hrecv]
        _ = 2 * Bform (coefC α) (restrictL u) (restrictL v) := NBform_iotaCot α hα hsumu hsumv
        _ = 2 * Bform (coefC α) (restrictLₗ u) (restrictLₗ v) := by
            rw [restrictLₗ_apply, restrictLₗ_apply]
  rw [htr, formNullity_smul_ne_zero (B := Bform (coefC α)) (by norm_num : (2 : ℂ) ≠ 0),
    ← nul_eq_formNullity]

/-! ### The eigenprojections as linear maps

The tan/cot eigenprojections `(I ∓ R_α)/2` are `ℂ`-linear on `Domς` (`R_α` is),
so they bundle into `↥Domς →ₗ[ℂ] (Idx→ℂ)` landing in `Dtan`/`Dcot` and summing to
the identity.  Applied to a `Domς`-radical subspace, they exhibit its projections
as block radicals — the `≤` half of the nullity block-split. -/

/-- The `tan`-eigenprojection `(I − R_α)/2` as a linear map on the domain. -/
def projTanₗ (α : ℝ) : ↥(Domς) →ₗ[ℂ] (Idx → ℂ) where
  toFun u := (2⁻¹ : ℂ) • ((u : Idx → ℂ) - rop α (u : Idx → ℂ))
  map_add' u v := by
    simp only [Submodule.coe_add]
    rw [rop_add α (sectorL2_of_mem_Domς u.2) (sectorL2_of_mem_Domς v.2)]
    module
  map_smul' c u := by
    simp only [Submodule.coe_smul, RingHom.id_apply]
    rw [rop_smul]
    module

/-- The `cot`-eigenprojection `(I + R_α)/2` as a linear map on the domain. -/
def projCotₗ (α : ℝ) : ↥(Domς) →ₗ[ℂ] (Idx → ℂ) where
  toFun u := (2⁻¹ : ℂ) • ((u : Idx → ℂ) + rop α (u : Idx → ℂ))
  map_add' u v := by
    simp only [Submodule.coe_add]
    rw [rop_add α (sectorL2_of_mem_Domς u.2) (sectorL2_of_mem_Domς v.2)]
    module
  map_smul' c u := by
    simp only [Submodule.coe_smul, RingHom.id_apply]
    rw [rop_smul]
    module

@[simp] lemma projTanₗ_apply (α : ℝ) (u : ↥Domς) :
    projTanₗ α u = (2⁻¹ : ℂ) • ((u : Idx → ℂ) - rop α (u : Idx → ℂ)) := rfl

@[simp] lemma projCotₗ_apply (α : ℝ) (u : ↥Domς) :
    projCotₗ α u = (2⁻¹ : ℂ) • ((u : Idx → ℂ) + rop α (u : Idx → ℂ)) := rfl

/-- The `tan`-projection lands in the `tan` block. -/
lemma projTanₗ_mem_Dtan (α : ℝ) (u : ↥Domς) : projTanₗ α u ∈ Dtan α := by
  have hSw : SectorL2 (u : Idx → ℂ) := sectorL2_of_mem_Domς u.2
  have hrw : rop α (u : Idx → ℂ) ∈ Domς := rop_mem_Domς α u.2
  have hSrw : SectorL2 (rop α (u : Idx → ℂ)) := sectorL2_of_mem_Domς hrw
  rw [projTanₗ_apply]
  refine ⟨Submodule.smul_mem _ _ (Submodule.sub_mem _ u.2 hrw), ?_⟩
  rw [rop_smul, rop_sub α hSw hSrw, rop_involutive α hSw, smul_sub, smul_sub]
  abel

/-- The `cot`-projection lands in the `cot` block. -/
lemma projCotₗ_mem_Dcot (α : ℝ) (u : ↥Domς) : projCotₗ α u ∈ Dcot α := by
  have hSw : SectorL2 (u : Idx → ℂ) := sectorL2_of_mem_Domς u.2
  have hrw : rop α (u : Idx → ℂ) ∈ Domς := rop_mem_Domς α u.2
  have hSrw : SectorL2 (rop α (u : Idx → ℂ)) := sectorL2_of_mem_Domς hrw
  rw [projCotₗ_apply]
  refine ⟨Submodule.smul_mem _ _ (Submodule.add_mem _ u.2 hrw), ?_⟩
  rw [rop_smul, rop_add α hSw hSrw, rop_involutive α hSw,
    add_comm (rop α (u : Idx → ℂ)) (u : Idx → ℂ)]

/-- The two eigenprojections sum to the identity. -/
lemma projTanₗ_add_projCotₗ (α : ℝ) (u : ↥Domς) :
    projTanₗ α u + projCotₗ α u = (u : Idx → ℂ) := by
  rw [projTanₗ_apply, projCotₗ_apply]
  module

/-! ### Nullity block-split

`𝓝_α` is block-diagonal on the `R_α`-eigenspaces, so its radical splits along the
two blocks.  Superadditivity (`≥`) is the mirror of the index argument (sum of two
block radicals is a `Domς` radical, disjoint so finranks add).  Subadditivity
(`≤`) uses the eigenprojections: a `Domς`-radical vector projects to block
radicals — no maximal-negative `(★)` needed, since a radical vector pairs to `0`
with everything. -/

/-- `𝓝_α` vanishes when its first slot is `0` (conjugate-linearity). -/
lemma NBform_zero_left (α : ℝ) (v : Idx → ℂ) : NBform α (0 : Idx → ℂ) v = 0 := by
  have h := NBform_smul_left α 0 (0 : Idx → ℂ) v
  simpa using h

/-- The `tan`-projection of a `Domς`-radical vector is radical in `Dtan`:
`𝓝_α(π_tan p, y) = 0` for every `y ∈ Dtan α`.  From `p = π_tan p + π_cot p`,
`𝓝_α(p, y) = 0` (radical) and `𝓝_α(π_cot p, y) = 0` (eigenspace orthogonality). -/
lemma projTanₗ_radical (α : ℝ) {V : Submodule ℂ (Idx → ℂ)}
    (hVrad : ∀ u ∈ V, ∀ v : Idx → ℂ, v ∈ Domς → NBform α u v = 0)
    (p : ↥Domς) (hpV : (p : Idx → ℂ) ∈ V) {y : Idx → ℂ} (hy : y ∈ Dtan α) :
    NBform α (projTanₗ α p) y = 0 := by
  set ut := projTanₗ α p with hut
  set uc := projCotₗ α p with huc
  have hutD : ut ∈ Dtan α := projTanₗ_mem_Dtan α p
  have hucD : uc ∈ Dcot α := projCotₗ_mem_Dcot α p
  have hutM : MemSectorς ut := mem_Domς.mp (Dtan_le_Domς α hutD)
  have hucM : MemSectorς uc := mem_Domς.mp (Dcot_le_Domς α hucD)
  have hyM : MemSectorς y := mem_Domς.mp (Dtan_le_Domς α hy)
  have hsum : ut + uc = (p : Idx → ℂ) := projTanₗ_add_projCotₗ α p
  have h0p : NBform α (p : Idx → ℂ) y = 0 := hVrad (p : Idx → ℂ) hpV y (Dtan_le_Domς α hy)
  have hyu : NBform α y uc = 0 :=
    NBform_eigen_orthogonal α (sectorL2_of_mem_Domς (Dtan_le_Domς α hy))
      (sectorL2_of_mem_Domς (Dcot_le_Domς α hucD)) hy.2 hucD.2
  have h0uc : NBform α uc y = 0 := by rw [NBform_conj_symm α y uc, hyu, map_zero]
  have hexp : NBform α (p : Idx → ℂ) y = NBform α ut y + NBform α uc y := by
    rw [← hsum, NBform_add_left α hutM hucM hyM]
  rw [h0p, h0uc, add_zero] at hexp
  exact hexp.symm

/-- The `cot`-projection of a `Domς`-radical vector is radical in `Dcot` (mirror;
the cross term `𝓝_α(π_tan p, y)` is a direct eigenspace orthogonality). -/
lemma projCotₗ_radical (α : ℝ) {V : Submodule ℂ (Idx → ℂ)}
    (hVrad : ∀ u ∈ V, ∀ v : Idx → ℂ, v ∈ Domς → NBform α u v = 0)
    (p : ↥Domς) (hpV : (p : Idx → ℂ) ∈ V) {y : Idx → ℂ} (hy : y ∈ Dcot α) :
    NBform α (projCotₗ α p) y = 0 := by
  set ut := projTanₗ α p with hut
  set uc := projCotₗ α p with huc
  have hutD : ut ∈ Dtan α := projTanₗ_mem_Dtan α p
  have hucD : uc ∈ Dcot α := projCotₗ_mem_Dcot α p
  have hutM : MemSectorς ut := mem_Domς.mp (Dtan_le_Domς α hutD)
  have hucM : MemSectorς uc := mem_Domς.mp (Dcot_le_Domς α hucD)
  have hyM : MemSectorς y := mem_Domς.mp (Dcot_le_Domς α hy)
  have hsum : ut + uc = (p : Idx → ℂ) := projTanₗ_add_projCotₗ α p
  have h0p : NBform α (p : Idx → ℂ) y = 0 := hVrad (p : Idx → ℂ) hpV y (Dcot_le_Domς α hy)
  have h0ut : NBform α ut y = 0 :=
    NBform_eigen_orthogonal α (sectorL2_of_mem_Domς (Dtan_le_Domς α hutD))
      (sectorL2_of_mem_Domς (Dcot_le_Domς α hy)) hutD.2 hy.2
  have hexp : NBform α (p : Idx → ℂ) y = NBform α ut y + NBform α uc y := by
    rw [← hsum, NBform_add_left α hutM hucM hyM]
  rw [h0p, h0ut, zero_add] at hexp
  exact hexp.symm

/-- **Superadditivity of the sector nullity**: `nul(Dtan) + nul(Dcot) ≤ nul(Domς)`.
A `tan`-block radical `V₁` and a `cot`-block radical `V₂` sum to a `𝓝_α`-radical
subspace of `Domς`: every `Domς` test vector splits into block parts
(`exists_eigen_decomp`), against which the four pairings vanish (own-block radical
+ cross-block eigenspace orthogonality).  Disjoint, so finranks add. -/
theorem formNullity_Dtan_add_Dcot_le (α : ℝ) :
    formNullity (NBform α) (Dtan α) + formNullity (NBform α) (Dcot α)
      ≤ formNullity (NBform α) Domς := by
  rw [formNullity_eq_biSup (NBform α) (Dtan α), formNullity_eq_biSup (NBform α) (Dcot α)]
  refine ENat.biSup_add_biSup_le'
    ⟨⊥, ⟨bot_le, fun u hu v hv => by rw [(Submodule.mem_bot ℂ).mp hu, NBform_zero_left]⟩,
      inferInstance⟩
    ⟨⊥, ⟨bot_le, fun u hu v hv => by rw [(Submodule.mem_bot ℂ).mp hu, NBform_zero_left]⟩,
      inferInstance⟩ ?_
  rintro V₁ ⟨hV₁, hfd₁⟩ V₂ ⟨hV₂, hfd₂⟩
  have := hfd₁; have := hfd₂
  have hdisj : V₁ ⊓ V₂ = ⊥ :=
    le_antisymm (le_trans (inf_le_inf hV₁.1 hV₂.1) (le_of_eq (Dtan_inf_Dcot α))) bot_le
  have hnull : NullOn (NBform α) Domς (V₁ ⊔ V₂) := by
    refine ⟨sup_le (le_trans hV₁.1 (Dtan_le_Domς α)) (le_trans hV₂.1 (Dcot_le_Domς α)), ?_⟩
    intro u hu y hy
    obtain ⟨u₁, hu₁, u₂, hu₂, rfl⟩ := Submodule.mem_sup.mp hu
    obtain ⟨yt, hyt, yc, hyc, rfl⟩ := exists_eigen_decomp α hy
    have hu₁D : u₁ ∈ Dtan α := hV₁.1 hu₁
    have hu₂D : u₂ ∈ Dcot α := hV₂.1 hu₂
    have hu₁M : MemSectorς u₁ := mem_Domς.mp (Dtan_le_Domς α hu₁D)
    have hu₂M : MemSectorς u₂ := mem_Domς.mp (Dcot_le_Domς α hu₂D)
    have hytM : MemSectorς yt := mem_Domς.mp (Dtan_le_Domς α hyt)
    have hycM : MemSectorς yc := mem_Domς.mp (Dcot_le_Domς α hyc)
    have z1 : NBform α u₁ yt = 0 := hV₁.2 u₁ hu₁ yt hyt
    have z2 : NBform α u₁ yc = 0 :=
      NBform_eigen_orthogonal α (sectorL2_of_mem_Domς (Dtan_le_Domς α hu₁D))
        (sectorL2_of_mem_Domς (Dcot_le_Domς α hyc)) hu₁D.2 hyc.2
    have z3 : NBform α u₂ yt = 0 := by
      have h := NBform_eigen_orthogonal α (sectorL2_of_mem_Domς (Dtan_le_Domς α hyt))
        (sectorL2_of_mem_Domς (Dcot_le_Domς α hu₂D)) hyt.2 hu₂D.2
      rw [NBform_conj_symm α yt u₂, h, map_zero]
    have z4 : NBform α u₂ yc = 0 := hV₂.2 u₂ hu₂ yc hyc
    rw [NBform_add_left α hu₁M hu₂M (memSectorς_add hytM hycM),
      NBform_add_right α hu₁M hytM hycM, NBform_add_right α hu₂M hytM hycM,
      z1, z2, z3, z4]
    ring
  have hfr : Module.finrank ℂ (V₁ ⊔ V₂ : Submodule ℂ (Idx → ℂ))
      = Module.finrank ℂ V₁ + Module.finrank ℂ V₂ := by
    have h := Submodule.finrank_sup_add_finrank_inf_eq V₁ V₂
    rw [hdisj, finrank_bot, add_zero] at h
    exact h
  have : FiniteDimensional ℂ (V₁ ⊔ V₂ : Submodule ℂ (Idx → ℂ)) :=
    Submodule.finiteDimensional_sup V₁ V₂
  calc (Module.finrank ℂ V₁ : ℕ∞) + Module.finrank ℂ V₂
      = Module.finrank ℂ (V₁ ⊔ V₂ : Submodule ℂ (Idx → ℂ)) := by rw [hfr]; push_cast; ring
    _ ≤ formNullity (NBform α) Domς :=
        le_iSup_of_le (V₁ ⊔ V₂) (le_iSup_of_le hnull (le_iSup_of_le ‹_› le_rfl))

/-- **Subadditivity of the sector nullity**: `nul(Domς) ≤ nul(Dtan) + nul(Dcot)`.
The eigenprojections carry a `Domς`-radical `V` into radical subspaces
`Vt ≤ Dtan`, `Vc ≤ Dcot` (`projTanₗ_radical`/`projCotₗ_radical`); the map
`x ↦ (π_tan x, π_cot x)` is injective (`π_tan + π_cot = id`), so
`finrank V ≤ finrank Vt + finrank Vc ≤ nul(Dtan) + nul(Dcot)`.  No `(★)`. -/
theorem formNullity_Domς_le_add (α : ℝ) :
    formNullity (NBform α) Domς
      ≤ formNullity (NBform α) (Dtan α) + formNullity (NBform α) (Dcot α) := by
  refine iSup_le fun V => iSup_le fun hV => iSup_le fun hfd => ?_
  have := hfd
  set emb : ↥V →ₗ[ℂ] ↥Domς := Submodule.inclusion hV.1 with hemb
  set gt : ↥V →ₗ[ℂ] (Idx → ℂ) := (projTanₗ α).comp emb with hgt
  set gc : ↥V →ₗ[ℂ] (Idx → ℂ) := (projCotₗ α).comp emb with hgc
  set Vt := LinearMap.range gt with hVtdef
  set Vc := LinearMap.range gc with hVcdef
  -- the two images are block radicals
  have hVt_null : NullOn (NBform α) (Dtan α) Vt := by
    refine ⟨?_, ?_⟩
    · intro x hx
      obtain ⟨p, rfl⟩ := hx
      exact projTanₗ_mem_Dtan α (emb p)
    · intro x hx y hy
      obtain ⟨p, rfl⟩ := hx
      exact projTanₗ_radical α hV.2 (emb p) p.2 hy
  have hVc_null : NullOn (NBform α) (Dcot α) Vc := by
    refine ⟨?_, ?_⟩
    · intro x hx
      obtain ⟨p, rfl⟩ := hx
      exact projCotₗ_mem_Dcot α (emb p)
    · intro x hx y hy
      obtain ⟨p, rfl⟩ := hx
      exact projCotₗ_radical α hV.2 (emb p) p.2 hy
  have hVtfd : FiniteDimensional ℂ Vt := LinearMap.finiteDimensional_range gt
  have hVcfd : FiniteDimensional ℂ Vc := LinearMap.finiteDimensional_range gc
  -- inject V into Vt × Vc via the two projections
  set Ft : ↥V →ₗ[ℂ] ↥Vt := gt.codRestrict Vt (fun x => LinearMap.mem_range_self gt x) with hFt
  set Fc : ↥V →ₗ[ℂ] ↥Vc := gc.codRestrict Vc (fun x => LinearMap.mem_range_self gc x) with hFc
  set g : ↥V →ₗ[ℂ] (↥Vt × ↥Vc) := Ft.prod Fc with hgdef
  have hg_inj : Function.Injective g := by
    rw [← LinearMap.ker_eq_bot, eq_bot_iff]
    intro x hx
    rw [Submodule.mem_bot]
    have h0 : g x = 0 := LinearMap.mem_ker.mp hx
    rw [hgdef, LinearMap.prod_apply, Prod.mk_eq_zero] at h0
    obtain ⟨hFtx, hFcx⟩ := h0
    have hgtv : projTanₗ α (emb x) = 0 := congrArg Subtype.val hFtx
    have hgcv : projCotₗ α (emb x) = 0 := congrArg Subtype.val hFcx
    have hsum : projTanₗ α (emb x) + projCotₗ α (emb x) = (x : Idx → ℂ) :=
      projTanₗ_add_projCotₗ α (emb x)
    have hx0 : (x : Idx → ℂ) = 0 := by
      rw [hgtv, hgcv, add_zero] at hsum
      exact hsum.symm
    exact Subtype.ext hx0
  have hfin : Module.finrank ℂ ↥V ≤ Module.finrank ℂ ((↥Vt) × (↥Vc)) :=
    LinearMap.finrank_le_finrank_of_injective hg_inj
  rw [Module.finrank_prod] at hfin
  calc (Module.finrank ℂ ↥V : ℕ∞)
      ≤ ((Module.finrank ℂ ↥Vt + Module.finrank ℂ ↥Vc : ℕ) : ℕ∞) := by exact_mod_cast hfin
    _ = (Module.finrank ℂ ↥Vt : ℕ∞) + (Module.finrank ℂ ↥Vc : ℕ∞) := by push_cast; ring
    _ ≤ formNullity (NBform α) (Dtan α) + formNullity (NBform α) (Dcot α) := by
        apply add_le_add
        · exact le_iSup_of_le Vt (le_iSup_of_le hVt_null (le_iSup_of_le hVtfd le_rfl))
        · exact le_iSup_of_le Vc (le_iSup_of_le hVc_null (le_iSup_of_le hVcfd le_rfl))

/-! ### The `iop-qop` nullity identity

Combining the two block-split directions with the block-nullity-equals-circle
transports gives the paper's `iop-qop_equiv` at the level of the nullity:

    nul(𝓝_{3,α}) = nul(𝒬_{tan(απ/2)}) + nul(𝒬_{cot(απ/2)}). -/
theorem formNullity_NBform_Domς (α : ℝ)
    (hαT : (1 : ℝ) + Real.cos (α * Real.pi) ≠ 0)
    (hαC : (1 : ℝ) - Real.cos (α * Real.pi) ≠ 0) :
    formNullity (NBform α) Domς = Statements.nul (coefT α) + Statements.nul (coefC α) := by
  refine le_antisymm ?_ ?_
  · calc formNullity (NBform α) Domς
        ≤ formNullity (NBform α) (Dtan α) + formNullity (NBform α) (Dcot α) :=
          formNullity_Domς_le_add α
      _ = Statements.nul (coefT α) + Statements.nul (coefC α) := by
          rw [formNullity_NBform_Dtan α hαT, formNullity_NBform_Dcot α hαC]
  · calc Statements.nul (coefT α) + Statements.nul (coefC α)
        = formNullity (NBform α) (Dtan α) + formNullity (NBform α) (Dcot α) := by
          rw [formNullity_NBform_Dtan α hαT, formNullity_NBform_Dcot α hαC]
      _ ≤ formNullity (NBform α) Domς := formNullity_Dtan_add_Dcot_le α

end KsIndex.SectorIndex
