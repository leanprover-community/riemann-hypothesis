module

public import Formalism.WindowSums.Statement
import Formalism.WindowSums.AnnihilatorPolynomials.EvalOneSmulDecomposition
import Formalism.WindowSums.AnnihilatorPolynomials.Lagrange
import Formalism.WindowSums.AnnihilatorPolynomials.ValProd
public import Formalism.WindowSums.AnnihilatorPolynomials.WindowSum
public import Formalism.WindowSums.AnnihilatorPolynomials.ZpowVal
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

namespace Formalism.WindowSums

theorem arc_ZpowVal : ZpowVal := valuation_zpow_sub_one
theorem arc_ValProd : ValProd := valProd_of valuation_zpow_sub_one
theorem arc_KillerVal : KillerVal := killerVal_of valuation_zpow_sub_one
theorem arc_KillerKills : KillerKills := annihilatorPoly_kills
theorem arc_WindowSum : WindowSum := sum_padicValInt_le
theorem arc_Lagrange : Lagrange := lagrange_annihilation

end Formalism.WindowSums
