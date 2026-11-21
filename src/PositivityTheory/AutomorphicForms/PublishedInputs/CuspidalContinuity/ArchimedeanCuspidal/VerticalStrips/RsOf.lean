import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.VerticalStrips.UnramifiedEulerProductIntegral
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RankinSelbergLocalFirstStatement
import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RankinSelbergLocalSecond
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RankinSelbergLocalFourth
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RankinSelbergThirdOfSecondFourth
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RankinSelbergFifthOfSecond
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RankinSelbergSixthOfEarlier
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RankinSelbergSeventhOfSecond
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.KernelFunctionalEquationOfTwoVariable
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RankinSelbergGammaFactor
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RankinSelbergFunctionalEquation
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RankinSelbergMeromorphicContinuationStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RankinSelbergLocalNonvanishing
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CongruenceSubgroupCosetDecompositionStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HeckeCosetRepresentatives
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NewformHeckeEigenvalue
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NewformTorusVanishingStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NewformMultiplicityOne
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NewformMultiplicityOneUnramified
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnramifiedRankinSelbergLocalFactorStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnramifiedWhittakerNewform
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GlobalRankinSelbergBasicFactsStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FundamentalDomainDescription
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FundamentalDomainInvarianceOfDescription
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FundamentalDomainIntegralCentralInvariance
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CentralCharacterIntegralProperties
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnfoldingBottomRowOrbits
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnfoldingMirabolicCosetsStatementStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnfoldingIntegralBottomRow
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EpsteinSeriesAbsoluteConvergence
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RankinSelbergUnfolding
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ZetaIntegralAbsoluteConvergence
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GlobalZetaIntegralConvergence
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GlobalZetaIntegralUnfolded
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EisensteinBasicFirst
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EisensteinBasicSecond
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EisensteinBasicThirdStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GaussianSchwartzBruhat
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SymplecticFourierGaussianStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ArchimedeanLocalIntegralStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GlobalFunctionalEquationH1
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NewformLiftExistence
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NewformLiftConductor
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NewformLiftLevelStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NewformLiftLevelCharacter
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NewformLiftLocalType
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NewformLiftHeckeEigenvalues
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NewformLiftWhittakerExpansion
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NewformLiftRapidDecay
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NewformLiftFourierCoefficientsStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NewformLiftCuspidality
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NewformLiftCuspForm
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NewformLiftLocalWhittaker
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EisensteinEulerProductStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RankinSelbergEulerProductPartial
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RankinSelbergEulerProduct
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HeckeProjectionEigenformStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RankinSelbergGlobalIdentity
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RankinSelbergGammaBound
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RankinSelbergArchimedeanFactor
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RankinSelbergLFunctionAnalytic
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RankinSelbergTheorem

section
namespace Ad3.R

theorem rs_asm
    (pA1 : A1)
    (pA2 : A2)
    (pA4 : A4)
    (pA3 : A2 → A4 → A3)
    (pA5 : A2 → A5)
    (pA6 : A1 → A3 → A4 → A5 → A6)
    (pA7 : A2 → A7)
    (pA8 : A7 → A8)
    (pA9g : LocalGammaFunctionalEquation)
    (pA9 : A1 → A6 → A8 → LocalGammaFunctionalEquation → A9)
    (pA10 : Loc2 → A10)
    (pA11 : Loc2 → A10 → A11)
    (pullbackOneCochains : C1)
    (pullbackZeroCochains : C0)
    (pU1 : C1 → U1)
    (pU0 : C1 → U0)
    (pM1 : A2 → C1 → M1)
    (pM0 : A2 → C1 → M0)
    (pE4 : Loc2 → E4)
    (pU2 : U2)
    (pB0 : B0)
    (pD0 : D0)
    (pG0 : D0 → G0)
    (pG1a : G1a)
    (pG1 : G1a → G1)
    (pG2a : G2a)
    (pG2b : G2b)
    (pG2c : G2b → G2c)
    (pG3a : G3a)
    (pG3 : G2a → G2b → G3a → G3)
    (pG4a : AdelicThetaPoissonSummation)
    (pG4 : G1a → G3 → AdelicThetaPoissonSummation → G4)
    (pG5 : G2c → G3 → G3a → G5)
    (lower_index_pair_unique : B0 → E1)
    (pE2 : B0 → E2)
    (pE3 : B0 → E3)
    (pGS : GS)
    (pFT : B0 → FT)
    (pE5 : E5)
    (deRhamH1Pullback : B0 → E2 → H1)
    (pF0 : B0 → F0)
    (pF0b : B0 → F0b)
    (pF1 : B0 → F1)
    (pF1b : B0 → AutomorphicLevelEquivariance)
    (pF3a : B0 → HeckeSumLocalTranslates)
    (pF3 : B0 → C0 → C1 → F0b → F1 → AutomorphicLevelEquivariance → HeckeSumLocalTranslates → F3)
    (pF2 : F2)
    (pF5 : B0 → F5)
    (pF4 : B0 → C1 → U2 → G0 → G1 → F0b → F1 → F2 → F3 → F5 → F4)
    (pF6 : F6)
    (pF6c : B0 → ConstantTermVanishingAlt)
    (pF7 : Loc2 → B0 → U0 → U1 → M0 → M1 → F0b → F1 → F2 → F3 → F4 → F7)
    (goodProjectorSmallestSpaceForms : B0 → M0 → F3 → E0)
    (pE6a : Loc2 → B0 → A10 → M0 → E4 → E0 → E1 → E2 → UnramifiedEulerProductIntegral)
    (pE6 : Loc2 → B0 → A10 → E2 → E3 → E5 → UnramifiedEulerProductIntegral → F2 → E6)
    (pG6 : B0 → C1 → G1 → F0b → F1 → F3 → F5 → G6)
    (pX0 : B0 → A1 → G0 → G2a → G4 → G5 → GS → FT → F2 → F5 → F6 → ConstantTermVanishingAlt → E6 → G6 → X0)
    (pX1g : RealPlaceGammaFactors)
    (pX1a : HalfPlaneAnalyticIdentities)
    (permutedRowProductSplitSum : Loc2 → B0 → A9 → LocalGammaFunctionalEquation → A10 → A11 → H1 → F0b → F1 → X0 → RealPlaceGammaFactors → HalfPlaneAnalyticIdentities → X1)
    (pTop : B0 → F0 → F1 → F7 → X1 → RS) :
    Loc2 → RS := by
  intro hLoc2
  have hA1 := pA1
  have hA2 := pA2
  have hA4 := pA4
  have hA3 := pA3 hA2 hA4
  have hA5 := pA5 hA2
  have hA6 := pA6 hA1 hA3 hA4 hA5
  have hA7 := pA7 hA2
  have hA8 := pA8 hA7
  have hA9g := pA9g
  have hA9 := pA9 hA1 hA6 hA8 hA9g
  have hA10 := pA10 hLoc2
  have hA11 := pA11 hLoc2 hA10
  have hC1 := pullbackOneCochains
  have hC0 := pullbackZeroCochains
  have hU1 := pU1 hC1
  have hU0 := pU0 hC1
  have hM1 := pM1 hA2 hC1
  have hM0 := pM0 hA2 hC1
  have hE4 := pE4 hLoc2
  have hU2 := pU2
  have hB0 := pB0
  have hD0 := pD0
  have hG0 := pG0 hD0
  have hG1a := pG1a
  have hG1 := pG1 hG1a
  have hG2a := pG2a
  have hG2b := pG2b
  have hG2c := pG2c hG2b
  have hG3a := pG3a
  have hG3 := pG3 hG2a hG2b hG3a
  have hG4a := pG4a
  have hG4 := pG4 hG1a hG3 hG4a
  have hG5 := pG5 hG2c hG3 hG3a
  have hE1 := lower_index_pair_unique hB0
  have hE2 := pE2 hB0
  have hE3 := pE3 hB0
  have hGS := pGS
  have hFT := pFT hB0
  have hE5 := pE5
  have hH1 := deRhamH1Pullback hB0 hE2
  have hF0 := pF0 hB0
  have hF0b := pF0b hB0
  have hF1 := pF1 hB0
  have hF1b := pF1b hB0
  have hF3a := pF3a hB0
  have hF3 := pF3 hB0 hC0 hC1 hF0b hF1 hF1b hF3a
  have hF2 := pF2
  have hF5 := pF5 hB0
  have hF4 := pF4 hB0 hC1 hU2 hG0 hG1 hF0b hF1 hF2 hF3 hF5
  have hF6 := pF6
  have hF6c := pF6c hB0
  have hF7 := pF7 hLoc2 hB0 hU0 hU1 hM0 hM1 hF0b hF1 hF2 hF3 hF4
  have hE0 := goodProjectorSmallestSpaceForms hB0 hM0 hF3
  have hE6a := pE6a hLoc2 hB0 hA10 hM0 hE4 hE0 hE1 hE2
  have hE6 := pE6 hLoc2 hB0 hA10 hE2 hE3 hE5 hE6a hF2
  have hG6 := pG6 hB0 hC1 hG1 hF0b hF1 hF3 hF5
  have hX0 := pX0 hB0 hA1 hG0 hG2a hG4 hG5 hGS hFT hF2 hF5 hF6 hF6c hE6 hG6
  have hX1g := pX1g
  have hX1a := pX1a
  have hX1 := permutedRowProductSplitSum hLoc2 hB0 hA9 hA9g hA10 hA11 hH1 hF0b hF1 hX0 hX1g hX1a
  have hTop := pTop hB0 hF0 hF1 hF7 hX1
  exact hTop

end Ad3.R
end

section
namespace Ad3.R

theorem rs_of : Ad3.Loc2 → Ad3.RS :=
  rs_asm
    (@GlobalTheory.T.rankin_selberg_local_first : Ad3.R.A1)
    (@GlobalTheory.T.rankin_selberg_local_second : Ad3.R.A2)
    (@GlobalTheory.T.rankin_selberg_local_fourth : Ad3.R.A4)
    (@GlobalTheory.T.rankin_selberg_third_of_second_fourth : Ad3.R.A2 → Ad3.R.A4 → Ad3.R.A3)
    (@GlobalTheory.T.rankin_selberg_fifth_of_second : Ad3.R.A2 → Ad3.R.A5)
    (@GlobalTheory.T.rankin_selberg_sixth_of_earlier : Ad3.R.A1 → Ad3.R.A3 → Ad3.R.A4 → Ad3.R.A5 → Ad3.R.A6)
    (@GlobalTheory.T.rankin_selberg_seventh_of_second : Ad3.R.A2 → Ad3.R.A7)
    (@GlobalTheory.T.kernel_functional_equation_of_two_variable : Ad3.R.A7 → Ad3.R.A8)
    (@GlobalTheory.T.rankin_selberg_gamma_factor : Ad3.R.LocalGammaFunctionalEquation)
    (@GlobalTheory.T.rankin_selberg_functional_equation : Ad3.R.A1 → Ad3.R.A6 → Ad3.R.A8 → Ad3.R.LocalGammaFunctionalEquation → Ad3.R.A9)
    (@GlobalTheory.T.rankin_selberg_meromorphic_continuation : Ad3.Loc2 → Ad3.R.A10)
    (@GlobalTheory.T.rankin_selberg_local_nonvanishing : Ad3.Loc2 → Ad3.R.A10 → Ad3.R.A11)
    (@GlobalTheory.T.congruence_subgroup_coset_decomposition : Ad3.R.C1)
    (@GlobalTheory.T.hecke_coset_representatives : Ad3.R.C0)
    (@GlobalTheory.T.newform_hecke_eigenvalue : Ad3.R.C1 → Ad3.R.U1)
    (@GlobalTheory.T.newform_torus_vanishing : Ad3.R.C1 → Ad3.R.U0)
    (@GlobalTheory.T.newform_multiplicity_one : Ad3.R.A2 → Ad3.R.C1 → Ad3.R.M1)
    (@GlobalTheory.T.newform_multiplicity_one_unramified : Ad3.R.A2 → Ad3.R.C1 → Ad3.R.M0)
    (@GlobalTheory.T.unramified_rankin_selberg_local_factor : Ad3.Loc2 → Ad3.R.E4)
    (@GlobalTheory.T.unramified_whittaker_newform : Ad3.R.U2)
    (@GlobalTheory.T.global_rankin_selberg_basic_facts : Ad3.R.B0)
    (@GlobalTheory.T.fundamental_domain_description : Ad3.R.D0)
    (@GlobalTheory.T.fundamental_domain_invariance_of_description : Ad3.R.D0 → Ad3.R.G0)
    (@GlobalTheory.T.fundamental_domain_integral_central_invariance : Ad3.R.G1a)
    (@GlobalTheory.T.central_character_integral_properties : Ad3.R.G1a → Ad3.R.G1)
    (@GlobalTheory.T.unfolding_bottom_row_orbits : Ad3.R.G2a)
    (@GlobalTheory.T.unfolding_mirabolic_cosets_statement : Ad3.R.G2b)
    (@GlobalTheory.T.unfolding_integral_bottom_row : Ad3.R.G2b → Ad3.R.G2c)
    (@GlobalTheory.T.epstein_series_absolute_convergence : Ad3.R.G3a)
    (@GlobalTheory.T.rankin_selberg_unfolding : Ad3.R.G2a → Ad3.R.G2b → Ad3.R.G3a → Ad3.R.G3)
    (@GlobalTheory.T.zeta_integral_absolute_convergence : Ad3.R.AdelicThetaPoissonSummation)
    (@GlobalTheory.T.global_zeta_integral_convergence : Ad3.R.G1a → Ad3.R.G3 → Ad3.R.AdelicThetaPoissonSummation → Ad3.R.G4)
    (@GlobalTheory.T.global_zeta_integral_unfolded : Ad3.R.G2c → Ad3.R.G3 → Ad3.R.G3a → Ad3.R.G5)
    (@GlobalTheory.T.eisenstein_basic_first : Ad3.R.B0 → Ad3.R.E1)
    (@GlobalTheory.T.eisenstein_basic_second : Ad3.R.B0 → Ad3.R.E2)
    (@GlobalTheory.T.eisenstein_basic_third : Ad3.R.B0 → Ad3.R.E3)
    (@GlobalTheory.T.gaussian_schwartz_bruhat : Ad3.R.GS)
    (@GlobalTheory.T.symplectic_fourier_gaussian : Ad3.R.B0 → Ad3.R.FT)
    (@GlobalTheory.T.archimedean_local_integral : Ad3.R.E5)
    (@GlobalTheory.T.global_functional_equation_h1 : Ad3.R.B0 → Ad3.R.E2 → Ad3.R.H1)
    (@GlobalTheory.T.newform_lift_existence : Ad3.R.B0 → Ad3.R.F0)
    (@GlobalTheory.T.newform_lift_conductor : Ad3.R.B0 → Ad3.R.F0b)
    (@GlobalTheory.T.newform_lift_level : Ad3.R.B0 → Ad3.R.F1)
    (@GlobalTheory.T.newform_lift_level_character : Ad3.R.B0 → Ad3.R.AutomorphicLevelEquivariance)
    (@GlobalTheory.T.newform_lift_local_type : Ad3.R.B0 → Ad3.R.HeckeSumLocalTranslates)
    (@GlobalTheory.T.newform_lift_hecke_eigenvalues : Ad3.R.B0 → Ad3.R.C0 → Ad3.R.C1 → Ad3.R.F0b → Ad3.R.F1 → Ad3.R.AutomorphicLevelEquivariance → Ad3.R.HeckeSumLocalTranslates → Ad3.R.F3)
    (@GlobalTheory.T.newform_lift_whittaker_expansion : Ad3.R.F2)
    (@GlobalTheory.T.newform_lift_rapid_decay : Ad3.R.B0 → Ad3.R.F5)
    (@GlobalTheory.T.newform_lift_fourier_coefficients : Ad3.R.B0 → Ad3.R.C1 → Ad3.R.U2 → Ad3.R.G0 → Ad3.R.G1 → Ad3.R.F0b → Ad3.R.F1 → Ad3.R.F2 → Ad3.R.F3 → Ad3.R.F5 → Ad3.R.F4)
    (@GlobalTheory.T.newform_lift_cuspidality : Ad3.R.F6)
    (@GlobalTheory.T.newform_lift_cusp_form : Ad3.R.B0 → Ad3.R.ConstantTermVanishingAlt)
    (@GlobalTheory.T.newform_lift_local_whittaker : Ad3.Loc2 → Ad3.R.B0 → Ad3.R.U0 → Ad3.R.U1 → Ad3.R.M0 → Ad3.R.M1 → Ad3.R.F0b → Ad3.R.F1 → Ad3.R.F2 → Ad3.R.F3 → Ad3.R.F4 → Ad3.R.F7)
    (@GlobalTheory.T.eisenstein_euler_product : Ad3.R.B0 → Ad3.R.M0 → Ad3.R.F3 → Ad3.R.E0)
    (@GlobalTheory.T.rankin_selberg_euler_product_partial : Ad3.Loc2 → Ad3.R.B0 → Ad3.R.A10 → Ad3.R.M0 → Ad3.R.E4 → Ad3.R.E0 → Ad3.R.E1 → Ad3.R.E2 → Ad3.R.UnramifiedEulerProductIntegral)
    (@GlobalTheory.T.rankin_selberg_euler_product : Ad3.Loc2 → Ad3.R.B0 → Ad3.R.A10 → Ad3.R.E2 → Ad3.R.E3 → Ad3.R.E5 → Ad3.R.UnramifiedEulerProductIntegral → Ad3.R.F2 → Ad3.R.E6)
    (@GlobalTheory.T.hecke_projection_eigenform : Ad3.R.B0 → Ad3.R.C1 → Ad3.R.G1 → Ad3.R.F0b → Ad3.R.F1 → Ad3.R.F3 → Ad3.R.F5 → Ad3.R.G6)
    (@GlobalTheory.T.rankin_selberg_global_identity : Ad3.R.B0 → Ad3.R.A1 → Ad3.R.G0 → Ad3.R.G2a → Ad3.R.G4 → Ad3.R.G5 → Ad3.R.GS → Ad3.R.FT → Ad3.R.F2 → Ad3.R.F5 → Ad3.R.F6 → Ad3.R.ConstantTermVanishingAlt → Ad3.R.E6 → Ad3.R.G6 → Ad3.R.X0)
    (@GlobalTheory.T.rankin_selberg_gamma_bound : Ad3.R.RealPlaceGammaFactors)
    (@GlobalTheory.T.rankin_selberg_archimedean_factor : Ad3.R.HalfPlaneAnalyticIdentities)
    (@GlobalTheory.T.rankin_selberg_l_function_analytic : Ad3.Loc2 → Ad3.R.B0 → Ad3.R.A9 → Ad3.R.LocalGammaFunctionalEquation → Ad3.R.A10 → Ad3.R.A11 → Ad3.R.H1 → Ad3.R.F0b → Ad3.R.F1 → Ad3.R.X0 → Ad3.R.RealPlaceGammaFactors → Ad3.R.HalfPlaneAnalyticIdentities → Ad3.R.X1)
    (@GlobalTheory.T.rankin_selberg_theorem : Ad3.R.B0 → Ad3.R.F0 → Ad3.R.F1 → Ad3.R.F7 → Ad3.R.X1 → Ad3.RS)

end Ad3.R
end
