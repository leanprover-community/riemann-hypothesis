module

public import Formalism.ThetaLogCoordinates.BihomogeneousPairs.LetterChainEmbeddings.PairStep
public import Formalism.ThetaLogCoordinates.BihomogeneousPairs.LetterChainEmbeddings.LatticeEqualHolds
public import Formalism.ThetaLogCoordinates.BihomogeneousPairs.LetterChainEmbeddings.LatticeLinearHolds
import Formalism.ThetaLogCoordinates.BihomogeneousPairs.LetterChainEmbeddings.LevelLatticeOf
import Formalism.ThetaLogCoordinates.BihomogeneousPairs.LetterChainEmbeddings.PlusOp
public import Formalism.ThetaLogCoordinates.BihomogeneousPairs.LetterChainEmbeddings.PstScalMem
import Formalism.ThetaLogCoordinates.BihomogeneousPairs.LetterChainEmbeddings.StepPlus
import Formalism.ThetaLogCoordinates.BihomogeneousPairs.LetterChainEmbeddings.StepTie
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
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

namespace Formalism.InvariantFactorPaths.KP.Top

open Formalism.InvariantFactorPaths.KP.LL

theorem pairStep : PairStep := pair_induction_holds
theorem latTie : LatTie := lattice_equal_holds
theorem latPlus : LatPlus := lattice_plus_holds
theorem plLin : PLLin := lattice_linear_holds
theorem commPL : CommPL := comm_lattice_holds
theorem paramPL : ParamPL := param_lattice_holds
theorem midTop : MidTop := middle_top_holds
theorem midPEq : MidPEq := middle_p_eq_holds
theorem stepTie : JoinCondition := StepTie_of pairStep latTie plLin commPL paramPL
theorem stepPlus : PlusCondition := StepPlus_of pairStep latPlus plLin commPL paramPL
theorem levelLattice : Formalism.GM.M.LevelLattice := LevelLattice_of midTop midPEq stepTie stepPlus

end Formalism.InvariantFactorPaths.KP.Top
