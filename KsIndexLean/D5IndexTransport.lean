module

public import KsIndexLean.D5DensityAssembly
public import KsIndexLean.NaturalCoreForm
public import KsIndexLean.FormIndexDensity

@[expose] public section


/-! # D5 index transport

The Jacobi sector form `sectorB` on a mixed character sector and its sesquilinearity, together with the
identification of the natural and reflected compact-core form indices with the sector `negativeIndex` of
`weakJacobi (surfacePotential k)` on `mixedCharacterDomain k r b₁ b₀` (`seamNat_eq_negativeIndex`,
`reflSeam_eq_negativeIndex`). These transport the core form index to the weak hemisphere index, below the
capstone census assembly. -/

noncomputable section
namespace KsIndex.Trace
open KsIndex.WeakH1 KsIndex.SingleDisk KsIndex.SingleDiskBridge KsIndex.FormIndex

variable {k : ℕ}

/-! ### The sector form `B` and its sesquilinearity -/

/-- The Jacobi form restricted to the common mixed weak sector. -/
def sectorB (k r : ℕ) (b₁ b₀ : Bool) :
    ↥(mixedCharacterDomain k r b₁ b₀) → ↥(mixedCharacterDomain k r b₁ b₀) → ℂ :=
  fun u v => weakJacobi (surfacePotential k) u.val v.val

set_option maxHeartbeats 1600000 in
lemma sectorB_sesq (k r : ℕ) (b₁ b₀ : Bool) :
    KsIndex.NegativeDensity.Sesq (sectorB k r b₁ b₀) where
  addL a b v := by
    simp only [sectorB, Submodule.coe_add, weakJacobi_add_left]
  addR a v w := by
    simp only [sectorB, Submodule.coe_add, weakJacobi_add_right]
  smulL c a v := by
    simp only [sectorB, SetLike.val_smul, weakJacobi_smul_left]
  smulR c a v := by
    simp only [sectorB, SetLike.val_smul, weakJacobi_smul_right]
  conj u v := by
    simp only [sectorB, weakJacobi_conj]
  continuous := by
    have h := (continuous_weakJacobi (surfacePotential k)).comp
      (Continuous.prodMk
        (continuous_subtype_val.comp (continuous_fst :
          Continuous fun p : ↥(mixedCharacterDomain k r b₁ b₀) ×
            ↥(mixedCharacterDomain k r b₁ b₀) => p.1))
        (continuous_subtype_val.comp continuous_snd))
    simpa only [sectorB, Function.comp_def] using h

/-! ### The two core indices on the common sector -/

/-- The natural core: `seamNat` — definitionally
`formIndex (Qd k) (NatCc ⊓ Erot1)` — equals the sector `negativeIndex`. -/
theorem seamNat_eq_negativeIndex (hk : 2 ≤ k) (r : ℕ) (b₁ b₀ : Bool) :
    seamNat k b₁ b₀ r
      = KsIndex.NegativeDensity.negativeIndex
          (fun x : ↥(mixedCharacterDomain k r b₁ b₀) => (sectorB k r b₁ b₀ x x).re) := by
  have hk1 : 1 ≤ k := by omega
  show formIndex (Qd k) (NatCc k b₁ b₀ ⊓ Erot1 k r) = _
  refine formIndex_eq_of_dense_form_map (Qd k) _ (sectorB_sesq k r b₁ b₀)
    (naturalCharacterToMixed hk1 r b₁ b₀)
    (naturalCharacterToMixed_denseRange hk1 r b₁ b₀) ?_
  intro x
  show Qd k x.val = (weakJacobi (surfacePotential k)
      (naturalCoreH1 hk1 ⟨x.val, x.property.1⟩)
      (naturalCoreH1 hk1 ⟨x.val, x.property.1⟩)).re
  rw [show naturalCoreH1 hk1 (⟨x.val, x.property.1⟩ :
        NatCc k b₁ b₀)
      = smoothToH1 (naturalCoreData hk1 ⟨x.val, x.property.1⟩) from rfl,
    smooth_weakJacobi_self_eq_Qd hk, Complex.ofReal_re]
  rfl

/-- The reflected core: the `ReflCc` sector form index equals the
same sector `negativeIndex`. -/
theorem reflSeam_eq_negativeIndex (hk : 2 ≤ k) (r : ℕ) (b₁ b₀ : Bool) :
    formIndex (Qd k)
        (KsIndex.TwistSwap.ReflCc k (sgn b₁) (sgn b₀) ⊓ Erot1 k r)
      = KsIndex.NegativeDensity.negativeIndex
          (fun x : ↥(mixedCharacterDomain k r b₁ b₀) => (sectorB k r b₁ b₀ x x).re) := by
  have hk1 : 1 ≤ k := by omega
  refine formIndex_eq_of_dense_form_map (Qd k) _ (sectorB_sesq k r b₁ b₀)
    (twistedCharacterToMixed hk1 r b₁ b₀)
    (twistedCharacterToMixed_denseRange hk1 r b₁ b₀) ?_
  intro x
  show Qd k x.val = (weakJacobi (surfacePotential k)
      (twistedCoreH1 hk1 ⟨x.val, x.property.1⟩)
      (twistedCoreH1 hk1 ⟨x.val, x.property.1⟩)).re
  rw [twistedCoreH1_form hk ⟨x.val, x.property.1⟩, Complex.ofReal_re]

end KsIndex.Trace
