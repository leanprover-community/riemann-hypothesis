module

public import Development.WeilBound.CoreStatements.AutomorphicKernels.UnitarySchrodingerModel.UnitarySchrodingerLemmas.LowRankSiegelDensities.Reduce
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ArchimedeanCoordinatesStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ArchimedeanFamilyContinuityStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ArchimedeanScalingStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ArchimedeanSectionStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DensityIntegralStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FinitePartOpenStatement
public import Development.WeilBound.CoreStatements.AutomorphicKernels.UnitarySchrodingerModel.UnitarySchrodingerLemmas.UnramifiedSchwartzDensity.Assemble
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

theorem PositivityTheory.PfSWUS.SchInf.schwartzDensInf : PositivityTheory.PfSWUS.HMass.SchwartzDensInf :=
  PositivityTheory.PfSWUS.SchInf.schwartzDensInf_of GlobalTheory.T.archimedean_family_continuity GlobalTheory.T.archimedean_section GlobalTheory.T.archimedean_coordinates GlobalTheory.T.archimedean_scaling GlobalTheory.T.finite_part_open
    GlobalTheory.T.density_integral
