module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LiftLambdaBound
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumComponentDegreesDivLeLatticeSlopeStatement
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Tactic.NormNum.Prime

@[expose] public section



section
open GlobalTheory.CovTop GlobalTheory.BigTop Formalism.MainNotions
namespace GlobalTheory.CovTop
theorem sumC_of_deepGood_alt : _root_.GlobalTheory.CovTop.DeepGoodness → _root_.GlobalTheory.CovTop.SumBoundCondition := fun h =>
  Closed.imp h fun _ _ _ ⟨C, h0, a, h⟩ => ⟨C, h0, a, fun x hx hle ι p hp i hi Y hY => by
    obtain ⟨-, -, -, h4, -, h6, -, h8⟩ := h x hx hle ι p hp i hi Y hY
    exact GlobalTheory.T.sum_component_degrees_div_le_latticeSlope _ p.T _ Y _ _ p.fw.laws ⟨Nat.le_add_left 1 _, hi.le⟩ hY.1 hY.2.1 hY.2.2 (uM p i) h4 h6 h8⟩
end GlobalTheory.CovTop
end
