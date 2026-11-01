module

/-
# Circle-form index and nullity as instances of the general form API

The circle definitions `Statements.ind` and `Statements.nul` agree
definitionally with `FormIndex.formIndex` and `FormIndex.formNullity` on
`Statements.Dom`. The bridge lemmas make these identifications explicit.

`ind_add_nul_le_one_via_generic` applies the general head-coordinate bound
with the singleton coordinate set `{0}`, corresponding to physical Fourier
frequency `1`. This gives a second derivation of the circle bound from the
shared form machinery. Other forms can use the same theorem by supplying
their domain, sesquilinear identities, and positivity away from their chosen
head coordinates.
-/
public import KsIndexLean.Statements
public import KsIndexLean.FormIndex

@[expose] public section


noncomputable section

namespace KsIndex.FormIndexBridge

open KsIndex.CircleQ KsIndex.Statements KsIndex.FormIndex

/-- The circle Morse index is the generic form index of `Qform s` on `Dom`. -/
lemma ind_eq_formIndex (s : ℝ) : ind s = formIndex (Qform s) Dom := rfl

/-- The circle nullity is the generic form nullity of `Bform s` on `Dom`. -/
lemma nul_eq_formNullity (s : ℝ) : nul s = formNullity (Bform s) Dom := rfl

/-- **Cross-check.**  The generic head-coordinate engine of `FormIndex.lean`,
fed the concrete `Bform`/`Qform` structure at the single head `ℓ = 1` (lattice
coordinate `n = 0`), reproduces `ind_add_nul_le_one` — the paper's
`qop_ind_plus_nul_above` — independently of the bespoke proof in
`Statements.lean`. -/
theorem ind_add_nul_le_one_via_generic (s : ℝ) : ind s + nul s ≤ 1 := by
  have hgen := formIndex_add_formNullity_le_card
    (Q := Qform s) (B := Bform s) (D := Dom) (F := ({0} : Finset ℤ))
    (Qform_zero s) (Bform_self s)
    (fun ha hb hv => Bform_add_left ha hb hv)
    (fun ha hv hw => Bform_add_right ha hv hw)
    (Bform_conj_symm s)
    (fun u hu hF hne =>
      Qform_pos_of_head_zero hu (hF 0 (Finset.mem_singleton_self 0)) hne)
  rw [ind_eq_formIndex, nul_eq_formNullity]
  simpa using hgen

end KsIndex.FormIndexBridge
