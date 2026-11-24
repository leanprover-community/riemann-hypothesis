module

public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.SiegelDensities.Pieces
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.SiegelDensities.DensEqOfPieces
public import Development.WeilBound.CoreStatements.AutomorphicKernels.UnitarySchrodingerModel.UnitarySchrodingerLemmas.LowRankSiegelDensities.MassTop
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.BinaryMassMeans.OneVecBinary
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

namespace PositivityTheory.SiegelWeilFormula.Densx

theorem densEq_of_base (hB : PositivityTheory.PfSWUS.HMass.SchwartzDensInf) (hBase : BaseOne) (hO : MassOne) :
    PositivityTheory.SiegelWeilFormula.Gen.DensEq :=
  densEq_of_pieces PositivityTheory.Rg.Mass.oneVecBinary PositivityTheory.PfSWUS.HMass.oneVecBinaryMass hB hBase hO

end PositivityTheory.SiegelWeilFormula.Densx

end
