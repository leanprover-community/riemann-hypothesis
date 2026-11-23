module

public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.BinaryMassMeans.MeanVal
public import Development.WeilBound.CoreStatements.AutomorphicKernels.UnitarySchrodingerModel.UnitarySchrodingerLemmas.LowRankSiegelDensities.SiegelDensitiesLowAOf
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CocompactnessStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CountingFormulaStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EquidistributionStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HassePrincipleStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LeftSideFormulaStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalMassFormulaStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MeanValueFormulaStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NormThetaMulStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OneVectorFormulaOfPartsStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SimilitudeInvarianceStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TestFunctionExistsStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.VectorLengthFormulaOfPartsStatement
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.BinaryMassMeans.SingleRowSide.Srside
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

namespace PositivityTheory.Rg.Mass

theorem e1 : E1 :=
  GlobalTheory.T.one_vector_formula_of_parts (GlobalTheory.T.vector_length_formula_of_parts GlobalTheory.T.cocompactness GlobalTheory.T.local_mass_formula) GlobalTheory.T.similitude_invariance GlobalTheory.T.hasse_principle
    (GlobalTheory.T.counting_formula GlobalTheory.T.test_function_exists (GlobalTheory.T.left_side_formula GlobalTheory.T.equidistribution GlobalTheory.T.cocompactness)
      (PositivityTheory.Rg.Mass.LiteralAutomorphy.srside (GlobalTheory.T.mean_value_formula GlobalTheory.T.equidistribution GlobalTheory.T.counting_bound_alt) GlobalTheory.T.local_mass_formula))

theorem oneVecBinary : PositivityTheory.PfSWUS.HMass.OneVecBinary := by
  intro F E _ _ _ _ _ σ hc M J hJ hM hA T hT hd
  subst hM
  exact e1 F E σ hc J hJ (fun x hx => by_contra fun h => hA x h hx) T hT hd

end PositivityTheory.Rg.Mass
