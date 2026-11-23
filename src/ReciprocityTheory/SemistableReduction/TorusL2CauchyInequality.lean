module

public import ReciprocityTheory.SemistableReduction.SphereLogIntegrableStatement
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
public import ReciprocityTheory.SemistableReduction.GramOfLinearOrder
public import ReciprocityTheory.SemistableReduction.HeightLowerBound
public import ReciprocityTheory.SemistableReduction.IntCores
public import ReciprocityTheory.SemistableReduction.LagrangeIdealLiftsFact
public import ReciprocityTheory.SemistableReduction.SJCore
public import ReciprocityTheory.SemistableReduction.SjHolds
public import ReciprocityTheory.SemistableReduction.SphereTorus
public import ReciprocityTheory.SemistableReduction.TorusLex
public import ReciprocityTheory.SemistableReduction.TorusMean

@[expose] public section

namespace ReciprocityTheory.MultiplicativeHeights.Closed

open ReciprocityTheory.MultiplicativeHeights

theorem sphereLinLog : SphereLinLogStatement := sjCore_holds

theorem sj : SJStatement := sj_holds sphereLinLog

theorem sphereLogIntegrable : SphereLogIntegrableStatement := sphereLogIntegrable_holds sj

theorem gauss_height_additivity : HeightAdditiveStatement := gauss_height_add_of_sphere sphereLogIntegrable

theorem sphere_height_lower_bound : HeightLowerBoundStatement := heightLowerBound_of_sj_of_sphereLogIntegrable sj sphereLogIntegrable

theorem torusMeanBasic : TorusMeanBasicStatement := torusMean_holds.1

theorem torusCoeff : TorusCoeffStatement := torusMean_holds.2

theorem torusLex : TorusLexStatement := (torusLex_holds torusMeanBasic torusCoeff).1

theorem torus_l2_cauchy_inequality : TorusL2Cauchy := (torusLex_holds torusMeanBasic torusCoeff).2

theorem gram : GramStatement := gram_holds torusMeanBasic torusLex torus_l2_cauchy_inequality

theorem sphereLeTorus : SphereLeTorusStatement := sphereTorus_holds sphereLogIntegrable torusMeanBasic

end ReciprocityTheory.MultiplicativeHeights.Closed
