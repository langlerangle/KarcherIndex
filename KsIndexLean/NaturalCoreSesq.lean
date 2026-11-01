module

public import KsIndexLean.NaturalCoreForm
public import KsIndexLean.ModeDiag
public import KsIndexLean.FormIndexSum

@[expose] public section


/-! The polarized disk form on the full natural test core.  Its linearity is
inherited from the weak H¹ realization, including the required integrability. -/
noncomputable section
namespace KsIndex.Trace
open KsIndex.WeakH1 KsIndex.SingleDisk KsIndex.SingleDiskBridge KsIndex.ModeDiag

lemma naturalCoreH1_polarized {k : ℕ} (hk : 1 ≤ k) {b1 b0 : Bool}
    (f g : NatCc k b1 b0) :
    weakJacobi (surfacePotential k) (naturalCoreH1 hk f) (naturalCoreH1 hk g) =
      Bd k f.val g.val := by
  exact smooth_weakJacobi_eq_classical (surfacePotential k)
    (naturalCoreData hk f) (naturalCoreData hk g)

/-- Sesquilinearity on the unrestricted natural core, before character decomposition. -/
theorem natCc_sesq {k : ℕ} (hk : 2 ≤ k) (b1 b0 : Bool) :
    FormIndex.Sesq (Qd k) (Bd k) (NatCc k b1 b0) where
  self := Bd_self_eq_Qd hk
  conj := fun u v => (Bd_conj_symm u v).symm
  addL := by
    intro a b v ha hb hv
    have h := weakJacobi_add_left (surfacePotential k)
      (naturalCoreH1 (by omega) ⟨a, ha⟩)
      (naturalCoreH1 (by omega) ⟨b, hb⟩)
      (naturalCoreH1 (by omega) ⟨v, hv⟩)
    rw [← naturalCoreH1_add, naturalCoreH1_polarized,
      naturalCoreH1_polarized, naturalCoreH1_polarized] at h
    exact h
  addR := by
    intro a v w ha hv hw
    have h := weakJacobi_add_right (surfacePotential k)
      (naturalCoreH1 (by omega) ⟨a, ha⟩)
      (naturalCoreH1 (by omega) ⟨v, hv⟩)
      (naturalCoreH1 (by omega) ⟨w, hw⟩)
    rw [← naturalCoreH1_add, naturalCoreH1_polarized,
      naturalCoreH1_polarized, naturalCoreH1_polarized] at h
    exact h
  smulR := by
    intro a v c ha hv
    have h := weakJacobi_smul_right (surfacePotential k) c
      (naturalCoreH1 (by omega) ⟨a, ha⟩)
      (naturalCoreH1 (by omega) ⟨v, hv⟩)
    rw [← naturalCoreH1_smul, naturalCoreH1_polarized,
      naturalCoreH1_polarized] at h
    exact h

end KsIndex.Trace
