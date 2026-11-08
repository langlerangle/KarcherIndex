module
public import KsIndexLean.ProdValid
public import KsIndexLean.AlphaLowProdValid
public import KsIndexLean.AlphaLowTreeBackend
@[expose] public section
namespace KsIndex.AlphaRemarkTrial.Energy4096Boundary
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000
set_option linter.style.longLine false
theorem sample_P_center : sampleNumerator 8192 = (309646837157863693234090970735761205842685266 : ℤ) := by
  have h : tableSampleNumerator KsIndex.PositiveEnergyAlphaLowProd.tFast 8192 = (309646837157863693234090970735761205842685266 : ℤ) := by
    rw [← KsIndex.AlphaLowTreeBackend.table_eq]
    decide +kernel
  have he := tableSampleNumerator_eq KsIndex.PositiveEnergyAlphaLowProd.valid
    (show SampleCovered 16389 8192 from by apply sampleCovered_of_bound; norm_num)
  exact he.symm.trans h
theorem sample_P_radius : sampleRadius 8192 = (4295899244775914968527382590086740173 : ℤ) := by
  have h : tableSampleRadius KsIndex.PositiveEnergyAlphaLowProd.tFast 8192 = (4295899244775914968527382590086740173 : ℤ) := by
    rw [← KsIndex.AlphaLowTreeBackend.table_eq]
    decide +kernel
  have he := tableSampleRadius_eq KsIndex.PositiveEnergyAlphaLowProd.valid
    (show SampleCovered 16389 8192 from by apply sampleCovered_of_bound; norm_num)
  exact he.symm.trans h
theorem energy_P_center :
    tableEnergyNumerator KsIndex.NegSignProd.t ({4096} : Finset ℤ) 1 0 = (2356471346170420296611019832251783968812336886853835088594826125025372813739043011820933101847 : ℤ) := by
  rw [tableEnergyNumerator_eq KsIndex.NegSignProd.valid ({4096} : Finset ℤ) 1 0
    (by intro n hn; simp only [Finset.mem_singleton] at hn; subst n; apply sampleCovered_of_bound; norm_num)]
  norm_num [energyNumerator, sample_P_center, sample_P_radius]
#print axioms energy_P_center
theorem energy_P_radius :
    tableEnergyRadius KsIndex.NegSignProd.t ({4096} : Finset ℤ) 1 0 = (65385221689900204473890656287466134757383205699073944775238678859948502897418026246211 : ℤ) := by
  rw [tableEnergyRadius_eq KsIndex.NegSignProd.valid ({4096} : Finset ℤ) 1 0
    (by intro n hn; simp only [Finset.mem_singleton] at hn; subst n; apply sampleCovered_of_bound; norm_num)]
  norm_num [energyRadius, sample_P_center, sample_P_radius]
#print axioms energy_P_radius
theorem sample_Mm_center : sampleNumerator 8193 = (847943563528515702939124659854412174515616938 : ℤ) := by
  have h : tableSampleNumerator KsIndex.PositiveEnergyAlphaLowProd.tFast 8193 = (847943563528515702939124659854412174515616938 : ℤ) := by
    rw [← KsIndex.AlphaLowTreeBackend.table_eq]
    decide +kernel
  have he := tableSampleNumerator_eq KsIndex.PositiveEnergyAlphaLowProd.valid
    (show SampleCovered 16389 8193 from by apply sampleCovered_of_bound; norm_num)
  exact he.symm.trans h
theorem sample_Mm_radius : sampleRadius 8193 = (1348105993359134877913369833338008214 : ℤ) := by
  have h : tableSampleRadius KsIndex.PositiveEnergyAlphaLowProd.tFast 8193 = (1348105993359134877913369833338008214 : ℤ) := by
    rw [← KsIndex.AlphaLowTreeBackend.table_eq]
    decide +kernel
  have he := tableSampleRadius_eq KsIndex.PositiveEnergyAlphaLowProd.valid
    (show SampleCovered 16389 8193 from by apply sampleCovered_of_bound; norm_num)
  exact he.symm.trans h
theorem energy_Mm_center :
    tableEnergyNumerator KsIndex.NegSignProd.t ({4096} : Finset ℤ) 4 1 = (17673223575718540455190936866424275995961611384915372640304148176982330012423293312923971807685 : ℤ) := by
  rw [tableEnergyNumerator_eq KsIndex.NegSignProd.valid ({4096} : Finset ℤ) 4 1
    (by intro n hn; simp only [Finset.mem_singleton] at hn; subst n; apply sampleCovered_of_bound; norm_num)]
  norm_num [energyNumerator, sample_Mm_center, sample_Mm_radius]
#print axioms energy_Mm_center
theorem energy_Mm_radius :
    tableEnergyRadius KsIndex.NegSignProd.t ({4096} : Finset ℤ) 4 1 = (56195670721758654504671681893866474160154254269176402019964600182817585945475517581391 : ℤ) := by
  rw [tableEnergyRadius_eq KsIndex.NegSignProd.valid ({4096} : Finset ℤ) 4 1
    (by intro n hn; simp only [Finset.mem_singleton] at hn; subst n; apply sampleCovered_of_bound; norm_num)]
  norm_num [energyRadius, sample_Mm_center, sample_Mm_radius]
#print axioms energy_Mm_radius
end KsIndex.AlphaRemarkTrial.Energy4096Boundary
