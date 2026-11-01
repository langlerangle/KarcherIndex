module

public import KsIndexLean.Surface

@[expose] public section


/-! Four-copy signs for odd reflection at height zero and even reflection at
height pi. The translation by one full period changes the sign. -/
noncomputable section
namespace KsIndex.Trace
open KsIndex.Surface

/-- Signs of the four half-period copies, ordered as in the disk chain. -/
def dnCopySign (n : ZMod 4) : ℂ := if n.val < 2 then 1 else -1

lemma dnCopySign_zero : dnCopySign 0 = 1 := by norm_num [dnCopySign]

lemma dnCopySign_norm (n : ZMod 4) : ‖dnCopySign n‖ = 1 := by
  unfold dnCopySign
  split <;> simp

lemma dnCopySign_add_two (n : ZMod 4) : dnCopySign (n + 2) = -dnCopySign n := by
  fin_cases n
  · change (-1 : ℂ) = -(1 : ℂ)
    rfl
  · change (-1 : ℂ) = -(1 : ℂ)
    rfl
  · change (1 : ℂ) = -(-1 : ℂ)
    simp
  · change (1 : ℂ) = -(-1 : ℂ)
    simp

/-- Adjacent copies have equal signs on Neumann seams and opposite signs on
Dirichlet seams, with the paper's n+1 parity convention. -/
lemma dnCopySign_successor (n : ZMod 4) :
    dnCopySign (n + 1) =
      (if (parity 2 (n + 1)).val = 1 then (1 : ℂ) else -1) * dnCopySign n := by
  fin_cases n
  · change (1 : ℂ) = 1 * 1
    simp
  · change (-1 : ℂ) = -1 * 1
    simp
  · change (-1 : ℂ) = 1 * -1
    simp
  · change (1 : ℂ) = -1 * -1
    simp

end KsIndex.Trace
