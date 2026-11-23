module

public import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.ThetaIdempotents.HeckeEta
public import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.ThetaIdempotents.MapsExist
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CoefficientDataExistsStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EisensteinHolomorphyOfHeightsStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FourierJacobiCoefficientOfBoundStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FourierJacobiEisensteinStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FourierJacobiUnfoldingStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FourierZeroHoldsStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HeckeCharacterEtaConditionStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HeightFunctionsExistStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JacobiMapsExistStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PartialConstantFourierCoefficientStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PartialConstantTermBoundStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PolarPartIdentityStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PoleRealityStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RegularSectionOfHeightsStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ResidueMeasureIdentityStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RightIdentityStatementStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SphericalBoundOfHeightsStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ThetaTotalOfHeckeEtaStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ThetaTwistIdentityStatement
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

namespace PositivityTheory.Rg.Rsw

theorem mapsExist : MapsExist := GlobalTheory.T.jacobi_maps_exist
theorem htExist : HtExist := GlobalTheory.T.height_functions_exist
theorem heckeEta : HeckeEta := GlobalTheory.T.hecke_character_eta_condition
theorem fjEis : FJEis := GlobalTheory.T.fourier_jacobi_eisenstein GlobalTheory.T.fourier_jacobi_unfolding GlobalTheory.T.theta_twist_identity
theorem pcBound : PcBound := GlobalTheory.T.partial_constant_term_bound
theorem rSec : RSec := GlobalTheory.T.regular_section_of_heights htExist
theorem eisHol : EisHol := GlobalTheory.T.eisenstein_holomorphy_of_heights htExist
theorem thTotal : ThTotal := GlobalTheory.T.theta_total_of_hecke_eta heckeEta
theorem cfFJ : CfFJ := GlobalTheory.T.fourier_jacobi_coefficient_of_bound pcBound
theorem pcFc : PcFc := GlobalTheory.T.partial_constant_fourier_coefficient mapsExist GlobalTheory.T.fourier_zero_holds
theorem sphBound : SphBound := GlobalTheory.T.spherical_bound_of_heights htExist
theorem resMu : ResMu :=
  GlobalTheory.T.residue_measure_identity mapsExist htExist heckeEta fjEis pcBound rSec eisHol thTotal pcFc sphBound GlobalTheory.T.fourier_zero_holds GlobalTheory.T.coefficient_data_exists
theorem polar : Polar :=
  GlobalTheory.T.polar_part_identity mapsExist htExist heckeEta GlobalTheory.T.right_identity_statement GlobalTheory.T.pole_reality fjEis pcBound rSec eisHol thTotal cfFJ pcFc sphBound

end PositivityTheory.Rg.Rsw
