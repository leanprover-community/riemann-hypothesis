module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.DimStatement
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.PropASt
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.SupLeL2PrincipalTorus
public import Development.AbelianVarietyTheory.Proofs.TorusSplitting.CharStatementHolds
public import Development.AbelianVarietyTheory.Proofs.TorusSplitting.ExtAllInputs
import Development.AbelianVarietyTheory.Proofs.TorusSplitting.GaussTailOfCardLe
public import Development.AbelianVarietyTheory.Proofs.TorusSplitting.GreedySplittingPrincipalTorusExistsStatement
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.ColEmpty
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.ContDiffOfDifferentiableFd
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.HfNormLeTwo
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.LemmaN
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.LemmaS
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.PaThDiffLe

@[expose] public section

open ReciprocityTheory.ChartRestriction.G.I2

namespace GlobalTheory.ThetaTorus

theorem gSup_holds : GSupStatement := gSup GlobalTheory.packingCount

theorem propA_holds : PropAStatement := propA GlobalTheory.packingCount GlobalTheory.gaussTail_of_card_le

theorem dim_holds : DimStatement := dim

theorem J_holds : JStatement :=
  jOf GlobalTheory.ext_all_inputs GlobalTheory.T.greedy_splitting_principal_torus_exists GlobalTheory.charStatement_holds
    (colTorus GlobalTheory.ext_all_inputs propA_holds gSup_holds)
    (colAbel GlobalTheory.ext_all_inputs propA_holds gSup_holds)
    (colEmpty GlobalTheory.ext_all_inputs propA_holds gSup_holds)

theorem N_holds : NStatement := lemmaN dim_holds

theorem I_holds : IStatement := iOf J_holds N_holds

end GlobalTheory.ThetaTorus
