module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenericMultOneDimOf
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.CuspidalInducedCharacter
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspidalIdempotentCharacters
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WhittakerSpaceDimParabolicInductionCuspidalEqOneStatement
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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

namespace GlobalTheory.GenericProduct

theorem oneGenericVector : OneGenericVector := GlobalTheory.T.whittakerSpaceDim_parabolicInduction_cuspidal_eq_one

theorem genericMultOne_holds : GlobalTheory.IndefiniteRowSideFullHecke.GenericMultiplicityOne.GenericMultOne := genericMultOne oneGenericVector

theorem oneWhittakerVector_holds : GlobalTheory.IndefiniteRowSideFullHecke.CuspidalInducedCharacter.OneWhittakerVector :=
  GlobalTheory.CuspidalIdempotentCharacters.genericMultOne_iff.1 genericMultOne_holds

end GlobalTheory.GenericProduct
