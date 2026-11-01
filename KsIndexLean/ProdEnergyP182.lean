module

public import KsIndexLean.ProdAccessor

@[expose] public section

/-! Energy chunk P182: window [3456,3519] of component (a,b)=(1,0). -/
namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
def wP182 : Finset ℤ := Finset.Ioc (3455) (3519)
theorem eP182_c : tableEnergyNumerator t wP182 1 0 = (192995612460071355318958845845873320515035168570529219883362043828916230107226678433642906409043 : ℤ) := by decide +kernel
theorem eP182_r : tableEnergyRadius t wP182 1 0 = (5538500494982115845898076529881571610655044031989782972104464645752780702731630490699287 : ℤ) := by decide +kernel
end KsIndex.NegSignProd
