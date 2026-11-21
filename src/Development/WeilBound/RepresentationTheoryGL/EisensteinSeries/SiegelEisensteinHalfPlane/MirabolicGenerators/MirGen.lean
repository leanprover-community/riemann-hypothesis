import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AverageMembership
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AverageInvariance
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnfoldingOfAverage
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DiagonalTermGood
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HeightTermGood
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.BoundaryTermGood
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MasterIdentity
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SideTermIdentity
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RatVSmul
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.VecKapMul
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ZetaIntegralOfEpsteinConv
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SideTermUnfolding
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SideTermConvergence
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TestFunctionSphericalK
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ZetaValueAtOne
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PrincipalIdentityAssembly
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MirabolicGeneration

namespace PositivityTheory.RgEis.MG

theorem mirGen : SecLaw → StdGood → BdetLaw → EpConv → EpMain → TestFun → TestSph → MirGen :=
  fun hS hG hB hC hM hT hSph =>
    have hO := GlobalTheory.T.side_term_identity hG hB
    have hZ := GlobalTheory.T.zeta_integral_of_epstein_conv hC
    GlobalTheory.T.mirabolic_generation hS hSph GlobalTheory.T.average_membership (GlobalTheory.T.average_invariance GlobalTheory.T.average_membership) hO (GlobalTheory.T.test_function_spherical_K hG hB hT)
      (GlobalTheory.T.principal_identity_assembly hM GlobalTheory.T.diagonal_term_good (GlobalTheory.T.master_identity GlobalTheory.T.average_membership GlobalTheory.T.diagonal_term_good GlobalTheory.T.height_term_good GlobalTheory.T.boundary_term_good) hO GlobalTheory.T.block_term_identity hZ
        (GlobalTheory.T.side_term_unfolding hC (GlobalTheory.T.unfolding_of_average hS GlobalTheory.T.average_membership) GlobalTheory.T.lines_decomposition GlobalTheory.T.block_term_identity hZ) (GlobalTheory.T.side_term_convergence hC hSph GlobalTheory.T.lines_decomposition GlobalTheory.T.block_term_identity) (GlobalTheory.T.zeta_value_at_one hM))

end PositivityTheory.RgEis.MG
