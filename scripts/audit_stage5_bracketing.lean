module

public import KsIndexLean

@[expose] public section

#print axioms KsIndex.Spectral.trial_bound_transport
#print axioms KsIndex.Spectral.eigenvalue_le_of_trial_inclusion
#print axioms KsIndex.Spectral.finiteH1Inclusion_injective
#print axioms KsIndex.Spectral.finiteCopy_infinite_eigenvalue_le
#print axioms KsIndex.Spectral.finiteCopy_finite_eigenvalue_le
#print axioms KsIndex.Spectral.finiteCopy_finite_to_infinite_eigenvalue_le
#print axioms KsIndex.Spectral.finiteCopy_infinite_to_finite_eigenvalue_le
#print axioms KsIndex.Spectral.slit_infinite_eigenvalue_bracket
#print axioms KsIndex.Spectral.slit_finite_eigenvalue_bracket

#print axioms KsIndex.Spectral.paperSlitCharacter_infinite_eigenvalue_bracket
#print axioms KsIndex.Spectral.paperSlitCharacter_finite_eigenvalue_bracket

#print axioms KsIndex.Spectral.strictSpectralCount_antitone
#print axioms KsIndex.Spectral.weakSpectralCount_antitone
#print axioms KsIndex.Spectral.finiteCopy_infinite_count_le
#print axioms KsIndex.Spectral.paperSlitCharacter_infinite_count_bracket

#print axioms KsIndex.Spectral.nonpositive_count_le_of_inclusion
#print axioms KsIndex.Spectral.finiteCopy_negativeIndex_le
#print axioms KsIndex.Spectral.finiteCopy_finite_nonpositive_count_le
#print axioms KsIndex.Spectral.finiteCopy_finite_negative_count_le
#print axioms KsIndex.Spectral.finiteCopy_finite_to_infinite_nonpositive_count_le
#print axioms KsIndex.Spectral.finiteCopy_finite_to_infinite_negative_count_le
#print axioms KsIndex.Spectral.finiteCopy_infinite_to_finite_nonpositive_count_le
#print axioms KsIndex.Spectral.finiteCopy_infinite_to_finite_negative_count_le

#print axioms KsIndex.Spectral.finiteCopy_indexNullity_infinite
#print axioms KsIndex.Spectral.finiteCopy_indexNullity_finite
#print axioms KsIndex.Spectral.finiteCopy_finite_indexNullity_le
#print axioms KsIndex.Spectral.finiteCopy_finite_to_infinite_indexNullity_le
#print axioms KsIndex.Spectral.finiteCopy_infinite_to_finite_indexNullity_le
#print axioms KsIndex.Spectral.finiteCopy_infinite_indexNullity_le
#print axioms KsIndex.Spectral.paperSlitCharacter_finite_indexNullity_bracket
#print axioms KsIndex.Spectral.paperSlitCharacter_infinite_indexNullity_bracket

#print axioms KsIndex.Spectral.slitNeumannReflectionEquiv
#print axioms KsIndex.Spectral.slitDirichletReflectionEquiv
#print axioms KsIndex.Spectral.weakJacobi_even_odd
#print axioms KsIndex.Spectral.slitNeumannReflection_jacobi
#print axioms KsIndex.Spectral.slitDirichletReflection_jacobi
#print axioms KsIndex.Spectral.even_odd_mem_iff
#print axioms KsIndex.Spectral.mem_pairCharacterDomain_iff
#print axioms KsIndex.Spectral.slitNeumannReflection_character
#print axioms KsIndex.Spectral.slitDirichletReflection_character
#print axioms KsIndex.Spectral.weightedMass_even_odd
#print axioms KsIndex.Spectral.slitNeumannSubspaceReflectionEquiv
#print axioms KsIndex.Spectral.paperSlitNeumannCharacterReflectionEquiv
#print axioms KsIndex.Spectral.slitDirichlet_subspace_eq
#print axioms KsIndex.Spectral.paperSlitDirichletCharacterReflectionEquiv
#print axioms KsIndex.Spectral.paperSlitNeumannCharacterReflection_jacobi
#print axioms KsIndex.Spectral.paperSlitNeumannCharacterReflection_mass
#print axioms KsIndex.Spectral.paperSlitDirichletCharacterReflection_jacobi
#print axioms KsIndex.Spectral.paperSlitDirichletCharacterReflection_mass
#print axioms KsIndex.Spectral.radical_product_tests
#print axioms KsIndex.Spectral.radicalProductEquiv
#print axioms KsIndex.Spectral.radicalProduct_finrank
#print axioms KsIndex.Spectral.pair_reflection_nullity
#print axioms KsIndex.Spectral.paperSlitNeumannCharacter_nullity
#print axioms KsIndex.Spectral.paperSlitDirichletCharacter_nullity
#print axioms KsIndex.Spectral.paperHemisphereCharacter_eq_NN
#print axioms KsIndex.Spectral.paperNeumannOddCharacter_eq_DN
#print axioms KsIndex.Spectral.paperDirichletEvenCharacter_eq_ND
#print axioms KsIndex.Spectral.paperDirichletOddCharacter_eq_DD
#print axioms KsIndex.Spectral.paperSlitNeumannCharacter_nullity_mixed
#print axioms KsIndex.Spectral.paperSlitDirichletCharacter_nullity_mixed
#print axioms KsIndex.Spectral.negative_product_dimension
#print axioms KsIndex.Spectral.negativeIndex_biSup
#print axioms KsIndex.Spectral.negativeIndex_add_le_product
#print axioms KsIndex.Spectral.negativeIndex_le_of_nonnegative_kernel
#print axioms KsIndex.Spectral.negativeIndex_product_upper
#print axioms KsIndex.Spectral.negativeIndex_product_eq_of_coordinates
#print axioms KsIndex.Spectral.diskNegativeCoordinates_kernel_nonnegative
#print axioms KsIndex.Spectral.diskNegativeCoordinates_dimension
#print axioms KsIndex.Spectral.diskJacobi_product_index_infinite
#print axioms KsIndex.Spectral.diskFiniteNegativeCoordinates_kernel_nonnegative
#print axioms KsIndex.Spectral.diskFiniteNegativeCoordinates_dimension
#print axioms KsIndex.Spectral.diskJacobi_product_index_finite
#print axioms KsIndex.Spectral.diskJacobi_product_index_finite_infinite
#print axioms KsIndex.Spectral.diskJacobi_product_index_infinite_finite
#print axioms KsIndex.Spectral.diskJacobi_product_index
#print axioms KsIndex.Spectral.pair_reflection_index
#print axioms KsIndex.Spectral.paperSlitNeumannCharacter_index
#print axioms KsIndex.Spectral.paperSlitDirichletCharacter_index
#print axioms KsIndex.Spectral.paperSlitNeumannCharacter_index_mixed
#print axioms KsIndex.Spectral.paperSlitDirichletCharacter_index_mixed
#print axioms KsIndex.Spectral.finiteCopy_common_eigenfunction_of_infinite_trial
#print axioms KsIndex.Spectral.finiteCopy_common_eigenfunction_of_finite_trial
#print axioms KsIndex.Spectral.finiteCopy_infinite_common_eigenfunction
#print axioms KsIndex.Spectral.finiteCopy_finite_common_eigenfunction
#print axioms KsIndex.Spectral.finiteCopy_finite_to_infinite_common_eigenfunction
#print axioms KsIndex.Spectral.finiteCopy_infinite_to_finite_common_eigenfunction
#print axioms KsIndex.JacobiFields.nu3_three_radial
#print axioms KsIndex.JacobiFields.nu3_three_radial_derivative
#print axioms KsIndex.JacobiFields.nu3_three_boundary
#print axioms KsIndex.JacobiFields.horizontal_three_boundary
#print axioms KsIndex.JacobiFields.horizontal_three_boundary_ne_zero
#print axioms KsIndex.JacobiFields.horizontal_three_formula
#print axioms KsIndex.JacobiFields.horizontal_three_radial
#print axioms KsIndex.JacobiFields.horizontal_three_radial_derivative
#print axioms KsIndex.Trace.globalSmoothH1_value
#print axioms KsIndex.Trace.globalSmoothH1_trace
#print axioms KsIndex.Trace.verticalThreeH1_value
#print axioms KsIndex.Trace.verticalThreeH1_trace
#print axioms KsIndex.Trace.horizontalThreeH1_trace
#print axioms KsIndex.Trace.horizontalThreeH1_trace_ne_zero_ae
#print axioms KsIndex.Trace.globalSmoothH1_dx
#print axioms KsIndex.Trace.globalSmoothH1_dy
#print axioms KsIndex.Trace.verticalThreeH1_zeroTrace
#print axioms KsIndex.Trace.verticalThreeH1_pair_all_value_phases
#print axioms KsIndex.Trace.first_green_global
#print axioms KsIndex.Trace.weakJacobi_globalSmooth_green
#print axioms KsIndex.Trace.fderiv_radial_of_hasDerivAt
#print axioms KsIndex.Trace.verticalThree_normal
#print axioms KsIndex.Trace.verticalThree_smooth_green
#print axioms KsIndex.Trace.verticalThree_smooth_trace_green
#print axioms KsIndex.Trace.slitFluxTestReal_smooth
#print axioms KsIndex.Trace.slitFluxTest_smooth
#print axioms KsIndex.Trace.slitFluxTest_rotation
#print axioms KsIndex.Trace.slitFluxTest_arc1_zero
#print axioms KsIndex.Trace.slitFluxTest_boundary_integral_pos
#print axioms KsIndex.Trace.slitFluxTest_boundary_integral_ne_zero
#print axioms KsIndex.Trace.slitFluxTestH1_arc1_zero
#print axioms KsIndex.Trace.slitFluxTestH1_character_zero
#print axioms KsIndex.Trace.slitFluxTestPair_mem_phase
#print axioms KsIndex.Trace.slitFluxTestPair_mem_character_zero
#print axioms KsIndex.Trace.verticalThree_phase_test_pairing
#print axioms KsIndex.Trace.verticalThree_phase_test_pairing_ne_zero
#print axioms KsIndex.Trace.verticalThree_not_phase_weak_kernel
#print axioms KsIndex.Trace.verticalThree_not_paper_weak_kernel
#print axioms KsIndex.Trace.paperPhase_ne_one
#print axioms KsIndex.Trace.verticalThree_phase_weak_scalar_zero
#print axioms KsIndex.Trace.verticalThree_paper_weak_scalar_zero
#print axioms KsIndex.Trace.verticalThree_span_paper_weak_zero
#print axioms KsIndex.Trace.boundaryArc_three_zero_measure_pos
#print axioms KsIndex.Trace.arcTrace_ne_zero_of_ae_nonzero
#print axioms KsIndex.Trace.horizontalThree_arc0_trace_ne_zero
#print axioms KsIndex.Trace.diagonal_pair_phase_eq_one
#print axioms KsIndex.Trace.horizontalThree_not_phase_domain
#print axioms KsIndex.Trace.horizontalThree_phase_scalar_zero
#print axioms KsIndex.Trace.horizontalThree_paper_scalar_zero
#print axioms KsIndex.Trace.horizontalThreeConjH1_trace
#print axioms KsIndex.Trace.horizontalThreeConjH1_trace_ne_zero_ae
#print axioms KsIndex.Trace.horizontalThreeConj_arc0_trace_ne_zero
#print axioms KsIndex.Trace.horizontalThreeConj_phase_scalar_zero
#print axioms KsIndex.Trace.horizontalThreeConj_paper_scalar_zero
#print axioms KsIndex.Trace.weakJacobi_C1_test_green
#print axioms KsIndex.Trace.naturalCoreH1_C1_representative
#print axioms KsIndex.Trace.verticalThree_naturalCore_green
#print axioms KsIndex.Trace.circleIntegral_eq_inner_one
#print axioms KsIndex.Trace.continuous_circleIntegral
#print axioms KsIndex.Trace.continuous_weakJacobi_fixed_left
#print axioms KsIndex.Trace.verticalThree_mixed_weak_green
#print axioms KsIndex.Trace.mem_trivial_NN_sector
#print axioms KsIndex.Trace.verticalThree_weak_green
#print axioms KsIndex.Trace.verticalThree_dirichlet_weak
#print axioms KsIndex.Trace.smooth_neumann_weak
#print axioms KsIndex.Trace.horizontalThree_combination_jacobi
#print axioms KsIndex.Trace.horizontalThree_normal
#print axioms KsIndex.Trace.horizontalThree_weak_neumann
#print axioms KsIndex.Trace.horizontalThree_conj_formula
#print axioms KsIndex.Trace.horizontalThreeConj_normal
#print axioms KsIndex.Trace.horizontalThreeConj_weak_neumann
#print axioms KsIndex.Trace.verticalThree_rotation
#print axioms KsIndex.Trace.horizontalThree_rotation
#print axioms KsIndex.Trace.third_negative_rotation_eq_xi
#print axioms KsIndex.Trace.xi_three_sq
#print axioms KsIndex.Trace.conj_zeta_three
#print axioms KsIndex.Trace.verticalThreeH1_character_zero
#print axioms KsIndex.Trace.horizontalThreeH1_character_one
#print axioms KsIndex.Trace.horizontalThreeConjH1_character_two
#print axioms KsIndex.Trace.verticalThree_pair_Dirichlet_character
#print axioms KsIndex.Trace.horizontalThree_pair_Neumann_character
#print axioms KsIndex.Trace.horizontalThreeConj_pair_Neumann_character
#print axioms KsIndex.Trace.slitDirichlet_difference_zeroTrace
#print axioms KsIndex.Trace.verticalThree_pair_Dirichlet_weak
#print axioms KsIndex.Trace.verticalThree_pair_Dirichlet_character_weak
#print axioms KsIndex.Trace.horizontalThree_pair_weak
#print axioms KsIndex.Trace.horizontalThreeConj_pair_weak
#print axioms KsIndex.Trace.horizontalThreeH1_ne_zero
#print axioms KsIndex.Trace.horizontalThreeConjH1_ne_zero
#print axioms KsIndex.Trace.verticalThreeH1_ne_zero
#print axioms KsIndex.Spectral.pair_nonzero_weak_kernel
#print axioms KsIndex.Spectral.paperDirichlet_zero_nontrivial_kernel
#print axioms KsIndex.Spectral.paperNeumann_one_nontrivial_kernel
#print axioms KsIndex.Spectral.paperNeumann_two_nontrivial_kernel
#print axioms KsIndex.Spectral.mixedCharacter_weak_index_eq_seamNat
#print axioms KsIndex.Spectral.pureDirichlet_weak_index_zero
#print axioms KsIndex.Spectral.pureNeumann_weak_index
#print axioms KsIndex.Spectral.three_pureNeumann_weak_index
#print axioms KsIndex.Spectral.three_slitNeumann_index_reduction
#print axioms KsIndex.Spectral.three_slitDirichlet_index_reduction
#print axioms KsIndex.Spectral.oppositeMixed_weak_index
#print axioms KsIndex.Spectral.mixedND_weak_index_one
#print axioms KsIndex.Spectral.mixedDN_weak_index_one
#print axioms KsIndex.Spectral.three_slitDirichlet_index_one
#print axioms KsIndex.Spectral.three_slitNeumann_index_two
#print axioms KsIndex.Spectral.pairWeakIndex_mono
#print axioms KsIndex.Spectral.three_paperSlit_phase_index_bounds
#print axioms KsIndex.Radial.eq_const_mul_uRad_complex
#print axioms KsIndex.Radial.eq_const_mul_uRad_complex_closed
#print axioms KsIndex.Radial.regular_dirichlet_nonzero_mode_vanishes
#print axioms KsIndex.Radial.uD_one
#print axioms KsIndex.Radial.uD_one_ne_zero
#print axioms KsIndex.Radial.regular_mode_neumann_coefficient
#print axioms KsIndex.Radial.regular_neumann_nonresonant_mode_vanishes
#print axioms KsIndex.Trace.interiorAnnulus_subset_disk
#print axioms KsIndex.Trace.interiorAnnulus_memLp
#print axioms KsIndex.Trace.interiorDisk_weak_polar
#print axioms KsIndex.Trace.interiorDiskRepresentative_continuousOn
#print axioms KsIndex.Trace.interiorDiskRepresentative_ae
#print axioms KsIndex.Trace.interiorDiskMode_continuousOn
#print axioms KsIndex.Trace.interiorDiskMode_sub_eq_integral
#print axioms KsIndex.Trace.interiorDiskMode_collar
#print axioms KsIndex.Trace.interiorDiskRepresentative_nested
#print axioms KsIndex.Trace.interiorDiskMode_nested
#print axioms KsIndex.Trace.complex_frame_pairing
#print axioms KsIndex.Trace.weakJet_polar_pairing
#print axioms KsIndex.Trace.weakDirichlet_polar_integral
#print axioms KsIndex.Trace.compactPolarTest_split
#print axioms KsIndex.Trace.compactPolarTest_smooth
#print axioms KsIndex.Trace.compactPolarTest_tsupport
#print axioms KsIndex.Trace.compactPolarTest_hasCompactSupport
#print axioms KsIndex.Trace.compactPolarTest_annular_support
#print axioms KsIndex.Trace.compactPolarTest_boundary_zero
#print axioms KsIndex.Trace.compactPolarTestH1_trace_zero
#print axioms KsIndex.Trace.compactPolarTestH1_zeroTrace
#print axioms KsIndex.Trace.compactPolarTest_slice
#print axioms KsIndex.Trace.compactPolarTest_radial_derivative
#print axioms KsIndex.Trace.compactPolarTest_fderiv_radial
#print axioms KsIndex.Trace.compactPolarTest_fderiv_angular
#print axioms KsIndex.Trace.globalSmoothH1_jet
#print axioms KsIndex.Trace.compactPolarTest_unit_radial
#print axioms KsIndex.Trace.compactPolarTestH1_radial_ae
#print axioms KsIndex.Trace.compactPolarTestH1_angular_ae
#print axioms KsIndex.Trace.weakDirichlet_compactPolarTest
#print axioms KsIndex.Trace.weakJacobi_compactPolarTest
#print axioms KsIndex.Trace.fourierTestLp_inner_unscaled
#print axioms KsIndex.Trace.integral_conj_mul_fourierAmbient
#print axioms KsIndex.Trace.slice_conj_fourier_pairing_ae
#print axioms KsIndex.Trace.interiorDiskMode_pairing_ae
#print axioms KsIndex.Trace.interiorDiskRadialMode_pairing_ae
#print axioms KsIndex.Trace.interiorDiskAngularField_memLp
#print axioms KsIndex.Trace.interior_angular_pairing_ae
#print axioms KsIndex.Trace.interior_angular_profile_pairing_ae
#print axioms KsIndex.Trace.interior_complex_angular_pairing_ae
#print axioms KsIndex.Trace.interior_angular_eigentest_ae
#print axioms KsIndex.Trace.interior_fourierTest_pairing_ae
#print axioms KsIndex.Trace.interior_angular_fourier_ae
#print axioms KsIndex.Trace.interior_angular_mode_ae
#print axioms KsIndex.Trace.interiorDiskAngularMode_pairing_ae
#print axioms KsIndex.Trace.integrableOn_compactPolarTest_mul
#print axioms KsIndex.Trace.integral_annulus_compactPolarTest_mul
#print axioms KsIndex.Trace.integral_compactPolarTest_mul
#print axioms KsIndex.Trace.integral_compactPolarTest_conj
#print axioms KsIndex.Trace.integral_compactPolarTest_value
#print axioms KsIndex.Trace.integral_compactPolarTest_radial
#print axioms KsIndex.Trace.integral_compactPolarTest_angular
#print axioms KsIndex.Trace.integral_compactPolarTest_radial_deriv
#print axioms KsIndex.Trace.compactPolarTest_radialProfile_twice
#print axioms KsIndex.Trace.integral_compactPolarTest_angular_weighted
#print axioms KsIndex.Trace.integrable_compactPolarTest_mul
#print axioms KsIndex.Trace.weakDirichlet_compactPolarTest_modes
#print axioms KsIndex.Trace.potential_compactPolarTest_modes
#print axioms KsIndex.Trace.weakJacobi_compactPolarTest_modes
#print axioms KsIndex.Trace.contDiff_Vrad
#print axioms KsIndex.Trace.surfaceJacobi_compactPolarTest_modes
#print axioms KsIndex.Trace.surfaceJacobi_weak_mode_equation
#print axioms KsIndex.Trace.integral_real_weight_conj
#print axioms KsIndex.Trace.surfaceJacobi_weak_mode_equation_normalized
#print axioms KsIndex.Trace.interiorDiskRadialMode_intervalIntegrable
#print axioms KsIndex.Trace.interiorDiskModeRHS_continuousOn
#print axioms KsIndex.Trace.surfaceJacobi_radial_flux_weak_deriv
#print axioms KsIndex.Trace.representative_hasDerivAt_of_continuousOn
#print axioms KsIndex.Trace.interiorDiskFluxRepresentative_continuousOn
#print axioms KsIndex.Trace.interiorDiskFluxRepresentative_hasDerivAt
#print axioms KsIndex.Trace.interiorDiskClassicalDerivative_continuousOn
#print axioms KsIndex.Trace.interiorDiskClassicalDerivative_ae
#print axioms KsIndex.Trace.interiorDiskMode_hasDerivAt
#print axioms KsIndex.Trace.interiorDiskMode_classical_flux_hasDerivAt
#print axioms KsIndex.Trace.interiorDiskClassicalDerivative_nested
#print axioms KsIndex.Trace.interiorDiskMode_overlap
#print axioms KsIndex.Trace.interiorDiskClassicalDerivative_overlap
#print axioms KsIndex.Trace.puncturedDiskMode_eq_interior
#print axioms KsIndex.Trace.puncturedDiskModeDerivative_eq_interior
#print axioms KsIndex.Trace.puncturedDiskMode_hasDerivAt
#print axioms KsIndex.Trace.puncturedDiskMode_flux_hasDerivAt
#print axioms KsIndex.Trace.puncturedDiskMode_continuousOn_annulus
#print axioms KsIndex.Trace.puncturedDiskModeDerivative_continuousOn_annulus
#print axioms KsIndex.Trace.puncturedDiskMode_one
#print axioms KsIndex.Trace.coefficient_weighted_energy_le
#print axioms KsIndex.Trace.interiorAnnulus_energy_le
#print axioms KsIndex.Trace.puncturedDiskMode_weighted_energy_le
#print axioms KsIndex.Trace.puncturedDiskModeDerivative_weighted_energy_le
#print axioms KsIndex.Trace.radialWronskian_hasDerivAt
#print axioms KsIndex.Trace.radialWronskian_eq_const
#print axioms KsIndex.Trace.radialWronskian_norm_sq_div_le
#print axioms KsIndex.Trace.eq_zero_of_log_bounds
#print axioms KsIndex.Trace.radialWronskian_eq_zero_of_energy
#print axioms KsIndex.Trace.eq_const_mul_of_radialWronskian_zero
#print axioms KsIndex.Trace.finite_energy_eq_const_mul_uRad
#print axioms KsIndex.Trace.puncturedDiskMode_eq_const_mul_uRad
#print axioms KsIndex.Trace.puncturedDiskMode_eq_const_mul_uRad_closed
#print axioms KsIndex.Trace.puncturedDiskMode_nonzero_boundary_formula
#print axioms KsIndex.Trace.weak_dirichlet_nonzero_mode_vanishes
#print axioms KsIndex.Trace.mem_fullZeroTrace_iff
#print axioms KsIndex.Trace.fullDirichlet_kernel_nonzero_modes

#print axioms KsIndex.Trace.circle_eq_of_coefficients_eq
#print axioms KsIndex.Trace.interiorDiskRepresentative_eq_of_modes
#print axioms KsIndex.Trace.interiorDiskProfile_ae_eq_of_punctured_modes

#print axioms KsIndex.Trace.ae_zero_of_sliceLp_zero
#print axioms KsIndex.Trace.ae_eq_of_sliceLp_eq
#print axioms KsIndex.Trace.complexH1_eq_of_punctured_modes

#print axioms KsIndex.Trace.interiorDiskProfile_smul_ae
#print axioms KsIndex.Trace.interiorDiskRepresentative_smul
#print axioms KsIndex.Trace.puncturedDiskMode_smul
#print axioms KsIndex.Trace.puncturedDiskMode_zero
#print axioms KsIndex.Trace.weak_dirichlet_eq_smul_of_nonzero
#print axioms KsIndex.Trace.fullDirichlet_kernel_eq_smul_vertical
#print axioms KsIndex.Trace.fullDirichlet_kernel_iff_smul_vertical

#print axioms KsIndex.Spectral.verticalDirichletVector_ne_zero
#print axioms KsIndex.Spectral.fullDirichlet_radical_eq_span
#print axioms KsIndex.Spectral.fullDirichlet_weakNullity_eq_one

#print axioms KsIndex.Trace.cubicCharacterTest_mem
#print axioms KsIndex.Trace.cubicCharacterTest_eigen
#print axioms KsIndex.Trace.cubicCharacterTest_pairing
#print axioms KsIndex.Trace.cubicCharacter_tests_suffice
#print axioms KsIndex.Trace.surfaceJacobi_character_test_rotation
#print axioms KsIndex.Trace.surfaceJacobi_cubic_tests_suffice

#print axioms KsIndex.Trace.diskRotation_neg_two_pi
#print axioms KsIndex.Trace.paperDiskRotation_cube
#print axioms KsIndex.Trace.diskRotation_mem_fullZeroTrace
#print axioms KsIndex.Trace.paperCharacter_cube
#print axioms KsIndex.Trace.paperCharacter_norm
#print axioms KsIndex.Trace.paperDirichlet_character_tests_extend
#print axioms KsIndex.Trace.paperNeumann_character_tests_extend
#print axioms KsIndex.Trace.paperDirichlet_character_kernel_spanned

#print axioms KsIndex.Trace.fullDirichletCharacter_kernel_zero_of_nontrivial
#print axioms KsIndex.Trace.fullDirichletCharacter_kernel_zero_of_not_dvd
#print axioms KsIndex.Trace.fullDirichletCharacter_zero_kernel_iff
#print axioms KsIndex.Spectral.fullDirichletCharacter_radical_zero
#print axioms KsIndex.Spectral.fullDirichletCharacter_zero_radical_span
#print axioms KsIndex.Spectral.fullDirichletCharacter_zero_nullity
#print axioms KsIndex.Spectral.fullDirichletCharacter_nontrivial_nullity
#print axioms KsIndex.Spectral.paperDirichletOddCharacter_eq_full
#print axioms KsIndex.Spectral.paperDirichletOddCharacter_zero_nullity
#print axioms KsIndex.Spectral.paperDirichletOddCharacter_nontrivial_nullity

#print axioms KsIndex.Trace.smooth_weak_green_of_flux
#print axioms KsIndex.Trace.weak_neumann_boundary_flux_orthogonal
#print axioms KsIndex.Trace.weak_neumann_fourier_trace_zero

#print axioms KsIndex.Trace.modeU_radial_ray
#print axioms KsIndex.Trace.modeU_normal
#print axioms KsIndex.Trace.conjugate_modeU_normal
#print axioms KsIndex.Trace.signedModeU_smooth
#print axioms KsIndex.Trace.signedModeU_normal
#print axioms KsIndex.Trace.signedModeU_flux_nonzero

#print axioms KsIndex.JacobiFields.laplacian_mul_pow_of_hasWD
#print axioms KsIndex.JacobiFields.laplacian_shift_mul_pow_of_hasWD
#print axioms KsIndex.JacobiFields.jacobi_shifted_Ffun
#print axioms KsIndex.Trace.modeU_eq_shifted_Ffun
#print axioms KsIndex.Trace.modeU_jacobi
#print axioms KsIndex.Trace.laplacian_conjugate
#print axioms KsIndex.Trace.signedModeU_jacobi
#print axioms KsIndex.Trace.weak_neumann_nonresonant_boundary_zero

#print axioms KsIndex.Trace.verticalThree_flux_pairing_ne_zero
#print axioms KsIndex.Trace.weak_neumann_zero_of_trace_zero
#print axioms KsIndex.Trace.weak_neumann_eq_of_trace_eq
#print axioms KsIndex.Trace.weak_neumann_eq_of_resonant_coefficients
#print axioms KsIndex.Trace.circleFourierCoeff_fourierAmbient
#print axioms KsIndex.Trace.horizontalThree_trace_coeff
#print axioms KsIndex.Trace.horizontalThreeConj_trace_coeff
#print axioms KsIndex.Trace.weak_neumann_eq_horizontal_combination
#print axioms KsIndex.Trace.weak_neumann_iff_horizontal_span

#print axioms KsIndex.Trace.paperCharacter_trace_coeff_zero
#print axioms KsIndex.Trace.paperHemisphere_kernel_full
#print axioms KsIndex.Trace.paperHemisphere_zero_kernel
#print axioms KsIndex.Trace.paperHemisphere_one_kernel_iff
#print axioms KsIndex.Trace.paperHemisphere_two_kernel_iff
#print axioms KsIndex.Spectral.paperHemisphere_zero_radical
#print axioms KsIndex.Spectral.paperHemisphere_one_radical
#print axioms KsIndex.Spectral.paperHemisphere_two_radical
#print axioms KsIndex.Spectral.paperHemisphere_zero_nullity
#print axioms KsIndex.Spectral.paperHemisphere_one_nullity
#print axioms KsIndex.Spectral.paperHemisphere_two_nullity

#print axioms KsIndex.Spectral.form_kernel_of_nonnegative_negative_complement
#print axioms KsIndex.Spectral.restricted_kernel_extends_of_negative_complement

#print axioms KsIndex.Spectral.nonnegative_complement_of_index_le_one
#print axioms KsIndex.Spectral.restricted_kernel_extends_of_index_le_one
#print axioms KsIndex.Spectral.exists_negative_of_index_ne_zero
#print axioms KsIndex.Spectral.restricted_kernel_extends_of_indices_one

#print axioms KsIndex.Spectral.disk_kernel_extends_of_index_one
#print axioms KsIndex.Spectral.paperNeumannOdd_kernel_extends
#print axioms KsIndex.Spectral.paperDirichletEven_kernel_extends
#print axioms KsIndex.Spectral.boundaryArc_three_one_measure_pos
#print axioms KsIndex.Spectral.horizontalThree_arc1_trace_ne_zero
#print axioms KsIndex.Spectral.horizontalThreeConj_arc1_trace_ne_zero
#print axioms KsIndex.Spectral.paperHemisphere_kernel_zero_of_arc
#print axioms KsIndex.Spectral.paperNeumannOdd_kernel_zero
#print axioms KsIndex.Spectral.paperDirichletEven_kernel_zero
#print axioms KsIndex.Spectral.paperNeumannOdd_radical_zero
#print axioms KsIndex.Spectral.paperNeumannOdd_nullity_zero
#print axioms KsIndex.Spectral.paperDirichletEven_radical_zero
#print axioms KsIndex.Spectral.paperDirichletEven_nullity_zero

#print axioms KsIndex.Spectral.three_slitNeumann_zero_nullity
#print axioms KsIndex.Spectral.three_slitNeumann_nontrivial_nullity
#print axioms KsIndex.Spectral.three_slitDirichlet_zero_nullity
#print axioms KsIndex.Spectral.three_slitDirichlet_nontrivial_nullity
#print axioms KsIndex.Spectral.three_slitNeumann_index_add_nullity
#print axioms KsIndex.Spectral.three_slitDirichlet_index_add_nullity
#print axioms KsIndex.Spectral.pair_reflection_kernel_iff
#print axioms KsIndex.Spectral.paperSlitNeumann_kernel_reflection_iff
#print axioms KsIndex.Spectral.paperSlitDirichlet_kernel_reflection_iff

#print axioms KsIndex.Spectral.paperSlitDirichlet_reflection_reconstruct
#print axioms KsIndex.Spectral.paperDirichletOdd_zero_kernel_span
#print axioms KsIndex.Spectral.paperSlitDirichlet_zero_kernel_span
#print axioms KsIndex.Spectral.paperSlitNeumann_one_kernel_span
#print axioms KsIndex.Spectral.paperSlitNeumann_two_kernel_span
#print axioms KsIndex.Spectral.paperSlitDirichlet_zero_common_kernel_zero
#print axioms KsIndex.Spectral.paperSlitNeumann_one_phase_kernel_zero
#print axioms KsIndex.Spectral.paperSlitNeumann_two_phase_kernel_zero

#print axioms KsIndex.Spectral.finiteCopy_indexNullity_le
#print axioms KsIndex.Spectral.paperSlitCharacter_indexNullity_bracket
#print axioms KsIndex.Spectral.three_paperSlit_zero_index_add_nullity
#print axioms KsIndex.Spectral.three_paperSlit_nontrivial_index_add_nullity_le_three

#print axioms KsIndex.Spectral.finite_eq_level_iff_count_interval
#print axioms KsIndex.Spectral.finiteCopy_infinite_zero_iff_index_interval
#print axioms KsIndex.Spectral.finiteCopy_finite_zero_iff_index_interval
#print axioms KsIndex.Spectral.finiteCopy_indexNullity_attained
#print axioms KsIndex.Spectral.finiteCopy_common_zero_of_index_interval

#print axioms KsIndex.Spectral.pair_common_zero_of_index_interval
#print axioms KsIndex.Spectral.three_paperSlit_zero_index_not_le_one
#print axioms KsIndex.Spectral.three_paperSlit_zero_index_two
#print axioms KsIndex.Spectral.three_paperSlit_zero_nullity_zero
#print axioms KsIndex.Spectral.three_paperSlit_nontrivial_total_ne_three
#print axioms KsIndex.Spectral.three_paperSlit_nontrivial_index_add_nullity_le_two

#print axioms KsIndex.Spectral.finiteCopy_infinite_positive_of_indexNullity_le
#print axioms KsIndex.Spectral.finiteCopy_finite_positive_of_indexNullity_le
#print axioms KsIndex.Spectral.three_paperSlit_index_add_nullity_le_two
#print axioms KsIndex.Spectral.three_paperSlit_infinite_third_positive
#print axioms KsIndex.Spectral.three_paperSlit_finite_third_positive
#print axioms KsIndex.Spectral.three_paperSlit_bracketing

#print axioms KsIndex.Spectral.characterRestrictionEquiv
#print axioms KsIndex.Spectral.slitSphericalCharacter
#print axioms KsIndex.Spectral.upperLower_character_iff
#print axioms KsIndex.Spectral.slitCharacterSphereEquiv
#print axioms KsIndex.Spectral.paperSlitCharacterSphereEquiv
#print axioms KsIndex.Spectral.slitCharacterSphere_jacobi
#print axioms KsIndex.Spectral.paperSlitCharacterSphere_jacobi

#print axioms KsIndex.Spectral.paperSlitCharacterSpectralCoordinates
#print axioms KsIndex.Spectral.paperSlitCharacterSpectralCoordinates_jacobi
#print axioms KsIndex.Spectral.paperSphericalCharacter_index_eq
#print axioms KsIndex.Spectral.paperSphericalCharacterRadical
#print axioms KsIndex.Spectral.mem_paperSphericalCharacterRadical
#print axioms KsIndex.Spectral.paperSphericalCharacterRadical_finrank
#print axioms KsIndex.Spectral.paperSphericalCharacterRadical_finiteDimensional
#print axioms KsIndex.Spectral.three_paperSpherical_zero_index_two
#print axioms KsIndex.Spectral.three_paperSpherical_zero_nullity_zero
#print axioms KsIndex.Spectral.three_paperSpherical_index_add_nullity_le_two
#print axioms KsIndex.Spectral.three_paperSpherical_index_ge_one

#print axioms KsIndex.Spectral.slitCharacterSphere_coordinates
#print axioms KsIndex.Spectral.paperSlitCharacterSpectralCoordinates_pair
#print axioms KsIndex.Spectral.paperSlitCharacterSpectralCoordinates_mass
#print axioms KsIndex.Spectral.paperSlitCharacterSolution_eigen_iff

#print axioms KsIndex.Spectral.trial_bound_equiv

#print axioms KsIndex.Spectral.paperSlitCharacter_trial_bound_iff

#print axioms KsIndex.Spectral.paperSphericalCharacter_infinite_minmax

#print axioms KsIndex.Spectral.paperSphericalCharacter_finite_minmax

#print axioms KsIndex.Trace.cyclic_invariant_tests_suffice

#print axioms KsIndex.Trace.cyclicCharacter_tests_suffice

#print axioms KsIndex.Trace.diskRotation_power

#print axioms KsIndex.Trace.cyclicDiskRotation_period

#print axioms KsIndex.Trace.cyclicCharacter_power

#print axioms KsIndex.Trace.cyclicCharacter_norm

#print axioms KsIndex.Trace.surfaceJacobi_cyclic_tests_suffice

#print axioms KsIndex.Trace.generalDirichlet_character_tests_extend

#print axioms KsIndex.Trace.radialDirichletH1

#print axioms KsIndex.Trace.radialDirichletH1_trace

#print axioms KsIndex.Trace.radialDirichletH1_rotation

#print axioms KsIndex.Trace.radialDirichletH1_weak

#print axioms KsIndex.Trace.radialDirichletH1_ne_zero

#print axioms KsIndex.Trace.generalDirichlet_kernel_span

#print axioms KsIndex.Trace.generalDirichlet_character_kernel_zero

#print axioms KsIndex.Spectral.form_nonnegative_of_index_zero

#print axioms KsIndex.Spectral.form_positive_of_index_zero_kernel_zero

#print axioms KsIndex.Trace.mixedDD_eq_fullDirichletCharacter

#print axioms KsIndex.Spectral.generalDirichlet_character_positive

#print axioms KsIndex.Spectral.generalDirichlet_character_positive_of_range

#print axioms KsIndex.Spectral.positive_of_attained_minmax

#print axioms KsIndex.Spectral.diskJacobi_infinite_positive_of_positive

#print axioms KsIndex.Spectral.diskJacobi_finite_positive_of_positive

#print axioms KsIndex.Spectral.generalDirichlet_infinite_eigenvalue_positive

#print axioms KsIndex.Spectral.generalDirichlet_finite_eigenvalue_positive

#print axioms KsIndex.Spectral.disk_infinite_eigenvalue_le

#print axioms KsIndex.Spectral.disk_finite_eigenvalue_le

#print axioms KsIndex.Spectral.disk_finite_to_infinite_eigenvalue_le

#print axioms KsIndex.Spectral.disk_infinite_to_finite_eigenvalue_le

#print axioms KsIndex.Spectral.linear_trial_orthogonal

#print axioms KsIndex.Spectral.disk_trial_orthogonal_before

#print axioms KsIndex.Spectral.disk_trial_orthogonal_finite

#print axioms KsIndex.Spectral.disk_common_eigenfunction_of_infinite_trial

#print axioms KsIndex.Spectral.disk_infinite_common_eigenfunction

#print axioms KsIndex.Spectral.disk_common_eigenfunction_of_finite_trial

#print axioms KsIndex.Spectral.disk_finite_to_infinite_common_eigenfunction

#print axioms KsIndex.Spectral.disk_infinite_to_finite_common_eigenfunction

#print axioms KsIndex.Spectral.disk_finite_common_eigenfunction

#print axioms KsIndex.Spherical.sphericalMassPotential

#print axioms KsIndex.Spherical.weightedDisk_mass_eq_potential

#print axioms KsIndex.Spherical.sphericalEigenPotential

#print axioms KsIndex.Spherical.sphericalEigenPotential_pairing

#print axioms KsIndex.Spherical.weakJacobi_sphericalEigenPotential

#print axioms KsIndex.Spherical.spherical_eigen_equation_iff

#print axioms KsIndex.Trace.radialJacobi_weak_mode_equation_normalized

#print axioms KsIndex.Trace.sphericalEigenRadialCoefficient

#print axioms KsIndex.Trace.sphericalEigenRadialCoefficient_smooth

#print axioms KsIndex.Trace.sphericalEigenPotential_radial

#print axioms KsIndex.Trace.sphericalEigen_weak_mode_equation

#print axioms KsIndex.Trace.eigenDiskModeRHS

#print axioms KsIndex.Trace.eigenDiskModeRHS_continuousOn

#print axioms KsIndex.Trace.sphericalEigen_radial_flux_weak_deriv

#print axioms KsIndex.Trace.eigenDiskFluxRepresentative

#print axioms KsIndex.Trace.eigenDiskClassicalDerivative

#print axioms KsIndex.Trace.eigenDiskFluxRepresentative_continuousOn

#print axioms KsIndex.Trace.eigenDiskFluxRepresentative_hasDerivAt

#print axioms KsIndex.Trace.eigenDiskClassicalDerivative_continuousOn

#print axioms KsIndex.Trace.eigenDiskClassicalDerivative_ae

#print axioms KsIndex.Trace.eigenDiskMode_hasDerivAt

#print axioms KsIndex.Trace.eigenDiskMode_classical_flux_hasDerivAt

#print axioms KsIndex.Trace.radialSystem_lipschitz

#print axioms KsIndex.Trace.radialSystem_zero_of_cauchy

#print axioms KsIndex.Trace.sphericalEigen_mode_zero_of_cauchy

#print axioms KsIndex.Trace.closedInterval_left_derivative

#print axioms KsIndex.Trace.radialSystem_zero_of_outer_cauchy

#print axioms KsIndex.Trace.sphericalEigen_mode_zero_of_outer_cauchy

#print axioms KsIndex.Trace.eigenDiskClassicalDerivative_nested

#print axioms KsIndex.Trace.eigenDiskClassicalDerivative_overlap

#print axioms KsIndex.Trace.eigenDiskFluxRepresentative_one

#print axioms KsIndex.Trace.sphericalEigen_eq_zero_of_boundary_cauchy

#print axioms KsIndex.Trace.sphericalEigen_radial_green
#print axioms KsIndex.Trace.sphericalEigen_normalMode_eq_green

#print axioms KsIndex.Trace.integrableOn_boundaryPolarTest_mul

#print axioms KsIndex.Trace.integral_annulus_boundaryPolarTest_conj

#print axioms KsIndex.Trace.integral_annulus_boundaryPolarTest_value

#print axioms KsIndex.Trace.integral_annulus_boundaryPolarTest_radial

#print axioms KsIndex.Trace.integral_annulus_boundaryPolarTest_angular

#print axioms KsIndex.Trace.integral_disk_boundaryPolarTest_mul

#print axioms KsIndex.Trace.integral_annulus_boundaryPolarTest_radial_deriv

#print axioms KsIndex.Trace.integral_annulus_boundaryPolarTest_angular_weighted

#print axioms KsIndex.Trace.weakDirichlet_boundaryPolarTest_modes

#print axioms KsIndex.Trace.potential_boundaryPolarTest_modes

#print axioms KsIndex.Trace.weakJacobi_boundaryPolarTest_modes

#print axioms KsIndex.Trace.radialJacobi_boundary_mode_equation_normalized

#print axioms KsIndex.Trace.sphericalEigen_boundary_mode_equation

#print axioms KsIndex.Trace.sphericalEigen_green_eq_mode_integrals

#print axioms KsIndex.Trace.sphericalEigen_neumann_flux_zero_of_cutoff

#print axioms KsIndex.Trace.sphericalEigen_neumann_flux_zero

#print axioms KsIndex.Trace.sphericalEigen_neumann_zeroTrace_eq_zero

#print axioms KsIndex.Trace.finite_laurent_eq_zero_of_infinite

#print axioms KsIndex.Trace.fourierAmbient_eq_zpow_on_circle

#print axioms KsIndex.Trace.finite_fourier_eq_zero_of_infinite

#print axioms KsIndex.Trace.finite_fourier_eq_zero_of_open_ae

#print axioms KsIndex.Trace.finite_nonzero_eigenfunctionals

#print axioms KsIndex.Trace.finite_fourier_support_of_invariant_finiteDimensional

#print axioms KsIndex.Trace.fourier_injective_of_irrational_rotation

#print axioms KsIndex.Trace.finite_fourier_support_of_irrational_invariance

#print axioms KsIndex.Trace.finite_fourier_support_of_rotation_invariance

#print axioms KsIndex.Trace.weightedDisk_mass_diskRotation

#print axioms KsIndex.Trace.sphericalEigen_rotation

#print axioms KsIndex.Trace.diskWeakEigenspace_rotation

#print axioms KsIndex.Trace.diskWeakEigenTraceSpace_finiteDimensional

#print axioms KsIndex.Trace.diskWeakEigenTraceSpace_rotation

#print axioms KsIndex.Trace.diskWeakEigenTraceSpace_finite_fourier_support

#print axioms KsIndex.Trace.sphericalEigen_trace_finite_support

#print axioms KsIndex.Trace.sphericalEigen_neumann_trace_finite_support

#print axioms KsIndex.Trace.circleFourierMode_coefficient

#print axioms KsIndex.Trace.circleFourierPolynomial_apply

#print axioms KsIndex.Trace.circleFourierPolynomial_coefficient

#print axioms KsIndex.Trace.circleL2_eq_finite_fourier

#print axioms KsIndex.Trace.circleL2_eq_zero_of_finite_support_open_ae

#print axioms KsIndex.Trace.sphericalEigen_neumann_openArc_eq_zero

#print axioms KsIndex.Trace.sphericalEigen_neumann_mem_zeroTrace_eq_zero

#print axioms KsIndex.Trace.sphericalEigenJacobi_diskRotation

#print axioms KsIndex.Trace.sphericalEigenJacobi_character_test_rotation

#print axioms KsIndex.Trace.sphericalEigen_cyclic_tests_suffice

#print axioms KsIndex.Trace.sphericalEigen_neumann_character_tests_extend

#print axioms KsIndex.Trace.sphericalEigen_neumann_character_openArc_eq_zero

#print axioms KsIndex.Spectral.neumann_character_eigenfunction_excluded

#print axioms KsIndex.Spectral.neumann_character_infinite_eigenvalue_lt

#print axioms KsIndex.Spectral.neumann_character_finite_to_infinite_eigenvalue_lt

#print axioms KsIndex.Spectral.neumann_character_infinite_to_finite_eigenvalue_lt

#print axioms KsIndex.Spectral.neumann_character_finite_eigenvalue_lt

#print axioms KsIndex.Trace.boundaryArc_one_nonempty

#print axioms KsIndex.Trace.boundaryArc_zero_nonempty

#print axioms KsIndex.Trace.mixedCharacterDomain_le_neumann

#print axioms KsIndex.Trace.mixedCharacterDomain_zero_arc

#print axioms KsIndex.Spectral.mixed_neumann_infinite_eigenvalue_lt

#print axioms KsIndex.Spectral.mixed_neumann_finite_to_infinite_eigenvalue_lt

#print axioms KsIndex.Spectral.mixed_neumann_infinite_to_finite_eigenvalue_lt

#print axioms KsIndex.Spectral.mixed_neumann_finite_eigenvalue_lt

#print axioms KsIndex.Trace.sphericalEigen_boundary_fourier_flux_pairing

#print axioms KsIndex.Trace.sphericalEigen_boundary_residual_flux_pairing

#print axioms KsIndex.Trace.weakJacobi_eq_of_trace_eq

#print axioms KsIndex.Trace.compactPolarTestH1_trace_eq_fourier

#print axioms KsIndex.Trace.sphericalEigen_fourier_extension_flux_pairing_of_cutoff

#print axioms KsIndex.Trace.sphericalEigen_fourier_extension_flux_pairing

#print axioms KsIndex.Trace.weakNormalFourierFunctional_eq

#print axioms KsIndex.Trace.smoothFourier_trace_eq

#print axioms KsIndex.Trace.smoothFourier_trace_rotation

#print axioms KsIndex.Trace.weakNormalFourierFunctional_rotation

#print axioms KsIndex.Trace.dirichlet_normal_functionals_finite

#print axioms KsIndex.Trace.sphericalEigen_dirichlet_normal_finite_support

#print axioms KsIndex.Trace.dirichletNormalPolynomial_coefficient

#print axioms KsIndex.Trace.dirichletNormalPolynomial_unique

#print axioms KsIndex.Trace.sphericalEigen_dirichlet_normal_openArc_eq_zero

#print axioms KsIndex.Trace.sphericalEigen_finite_trace_pairing

#print axioms KsIndex.Trace.circleFourierModeContinuous_toLp

#print axioms KsIndex.Trace.inner_circleFourierPolynomial

#print axioms KsIndex.Trace.sphericalEigen_normal_pairing_finite_trace

#print axioms KsIndex.Trace.sphericalEigen_normal_pairing_closure

#print axioms KsIndex.Trace.continuous_planeRotation_parameter

#print axioms KsIndex.Trace.continuous_diskLpRotation

#print axioms KsIndex.Trace.rotatedColumn_eq

#print axioms KsIndex.Trace.continuous_rotatedColumn

#print axioms KsIndex.Trace.continuous_diskRotation

#print axioms KsIndex.Trace.map_fourierCoeffOn

#print axioms KsIndex.Trace.diskAngularProjection_map

#print axioms KsIndex.Trace.fourierCoeffOn_fourier

#print axioms KsIndex.Trace.diskAngularProjection_trace_coefficient

#print axioms KsIndex.Trace.diskAngularProjection_mem_finiteFourierTraceTests

#print axioms KsIndex.Trace.continuous_eq_zero_at_zero_of_fourierCoeffOn

#print axioms KsIndex.Trace.finiteFourierTraceTests_annihilator

#print axioms KsIndex.Trace.sphericalEigen_dirichlet_normal_weak_green

#print axioms KsIndex.Trace.circleFourierPolynomialAmbient_smooth

#print axioms KsIndex.Trace.circleFourierPolynomialAmbient_circle

#print axioms KsIndex.Trace.dirichletNormalPolynomial_has_smooth_extension

#print axioms KsIndex.Trace.circle_weighted_norm_zero

#print axioms KsIndex.Trace.weighted_normal_test_pairing

#print axioms KsIndex.Trace.sphericalEigen_normal_zero_of_weighted_test

#print axioms KsIndex.Trace.mixedArcWeight_smooth

#print axioms KsIndex.Trace.mixedArcWeight_nonneg

#print axioms KsIndex.Trace.mixedArcWeight_pos

#print axioms KsIndex.Trace.mixedArcWeight_zero

#print axioms KsIndex.Trace.mixedArcWeight_test_mem

#print axioms KsIndex.Trace.sphericalEigen_dirichlet_mixed_eq_zero

#print axioms KsIndex.Trace.cyclicAngle_exp_power

#print axioms KsIndex.Trace.mixedTraceDomain_cyclic_rotation

#print axioms KsIndex.Trace.fullZeroTrace_le_mixed

#print axioms KsIndex.Trace.sphericalEigen_dirichlet_mixed_character_eq_zero

#print axioms KsIndex.Spectral.mixedDD_le_mixed

#print axioms KsIndex.Spectral.mixed_dirichlet_eigenfunction_excluded

#print axioms KsIndex.Spectral.mixed_dirichlet_infinite_eigenvalue_lt

#print axioms KsIndex.Spectral.mixed_dirichlet_finite_to_infinite_eigenvalue_lt

#print axioms KsIndex.Spectral.mixed_dirichlet_infinite_to_finite_eigenvalue_lt

#print axioms KsIndex.Spectral.mixed_dirichlet_finite_eigenvalue_lt
