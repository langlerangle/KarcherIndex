module

public import KsIndexLean.JoinedSeamIntegrability
public import KsIndexLean.WeakSesquilinearEquation

@[expose] public section


/-! The actual pair radical supplies the full weak Jacobi equation across
both seam families. No smooth representative or conditional PDE input remains. -/
noncomputable section
namespace KsIndex.PaperSlitTransport
open KsIndex.Trace KsIndex.PaperSlitAdapter KsIndex.Surface

theorem pair_radical_seam_weak_equation {α : ℝ} {j : ℕ}
    (u : paperSlitCharacterDomain α j) (hrad : ∀ w, Bpair u w = 0) :
    let c := Complex.exp ((2 * Real.pi * α) * Complex.I)
    Weq.InteriorWeakEquation (seamDomain (boundaryArc 3 0) (isOpen_boundaryArc 3 0))
      (fun z => joinedDiskJet u.val.1 u.val.2 c z 1)
      (fun z => joinedDiskJet u.val.1 u.val.2 c z Complex.I)
      (fun z => (potV 3 z : ℂ) * joinedDiskValue u.val.1 u.val.2 c z) := by
  dsimp only
  apply Weq.interiorWeakEquation_of_sesquilinear
  intro ψ
  have he := joined_integrals_split (isOpen_boundaryArc 3 0) u.val.1 u.val.2
    (Complex.exp ((2 * Real.pi * α) * Complex.I)) ψ
  rw [pair_radical_joined_halves_test u hrad ψ] at he
  exact sub_eq_zero.mp he

theorem pair_radical_seam_one_weak_equation {α : ℝ} {j : ℕ}
    (u : paperSlitCharacterDomain α j) (hrad : ∀ w, Bpair u w = 0) :
    Weq.InteriorWeakEquation (seamDomain (boundaryArc 3 1) (isOpen_boundaryArc 3 1))
      (fun z => joinedDiskJet u.val.1 u.val.2 1 z 1)
      (fun z => joinedDiskJet u.val.1 u.val.2 1 z Complex.I)
      (fun z => (potV 3 z : ℂ) * joinedDiskValue u.val.1 u.val.2 1 z) := by
  apply Weq.interiorWeakEquation_of_sesquilinear
  intro ψ
  have he := joined_integrals_split (isOpen_boundaryArc 3 1) u.val.1 u.val.2 1 ψ
  rw [pair_radical_joined_halves_one_test u hrad ψ] at he
  exact sub_eq_zero.mp he

end KsIndex.PaperSlitTransport
