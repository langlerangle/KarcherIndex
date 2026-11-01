module

public import KsIndexLean.ProdAccessor

@[expose] public section

/-! Energy chunk P154: window [1664,1727] of component (a,b)=(1,0). -/
namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
def wP154 : Finset ℤ := Finset.Ioc (1663) (1727)
theorem eP154_c : tableEnergyNumerator t wP154 1 0 = (562379421686566793963370951334025369755786899467569450452219860995170456927403244372916557164247 : ℤ) := by decide +kernel
theorem eP154_r : tableEnergyRadius t wP154 1 0 = (19139053425476217302981010546014028073911403649821552425383781362487718750316328427812565 : ℤ) := by decide +kernel
end KsIndex.NegSignProd
