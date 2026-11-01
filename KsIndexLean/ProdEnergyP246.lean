module

public import KsIndexLean.ProdAccessor

@[expose] public section

/-! Energy chunk P246: window [7552,7615] of component (a,b)=(1,0). -/
namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
def wP246 : Finset ℤ := Finset.Ioc (7551) (7615)
theorem eP246_c : tableEnergyNumerator t wP246 1 0 = (57405837740457113004021230159522654689252402077090379966712888684247808750567327817209327613369 : ℤ) := by decide +kernel
theorem eP246_r : tableEnergyRadius t wP246 1 0 = (1416669729016831457036205759376884686231238884733693171543532531339387043039899711223877 : ℤ) := by decide +kernel
end KsIndex.NegSignProd
