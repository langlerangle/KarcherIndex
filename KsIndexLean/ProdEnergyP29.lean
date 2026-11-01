module

public import KsIndexLean.ProdAccessor

@[expose] public section

/-! Energy chunk P29: window [-6336,-6273] of component (a,b)=(1,0). -/
namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
def wP29 : Finset ℤ := Finset.Ioc (-6337) (-6273)
theorem eP29_c : tableEnergyNumerator t wP29 1 0 = (746208152659799348532188308233657233266305836466393048335388204363640911124000495396665121247051 : ℤ) := by decide +kernel
theorem eP29_r : tableEnergyRadius t wP29 1 0 = (6113718000201278318137512436761358022251731091213568037835218200715826618490541459416916 : ℤ) := by decide +kernel
end KsIndex.NegSignProd
