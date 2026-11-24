module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.AdDecompK
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKawayAw
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKawayDec
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKawayFinTop
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKfourW
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



section
namespace PositivityTheory.SiegelWeilFormula.KAway
theorem awayAct_of_tAll_k (hT : _root_.PositivityTheory.SiegelWeilFormula.TAll_k) : _root_.PositivityTheory.SiegelWeilFormula.AwayAct_k :=
  _root_.PositivityTheory.SiegelWeilFormula.KAway.awayAct_of_k hT _root_.PositivityTheory.SiegelWeilFormula.kfour.auxiliaryExistence_holds _root_.PositivityTheory.SiegelWeilFormula.KAway.adDecomp_k
theorem finAct_of_tAll_k (hT : _root_.PositivityTheory.SiegelWeilFormula.TAll_k) : _root_.PositivityTheory.SiegelWeilFormula.FinAct_k :=
  _root_.PositivityTheory.SiegelWeilFormula.KAway.finAct_of_k hT _root_.PositivityTheory.SiegelWeilFormula.kfour.auxiliaryExistence_holds _root_.PositivityTheory.SiegelWeilFormula.KAway.adDecomp_k
end PositivityTheory.SiegelWeilFormula.KAway
end
