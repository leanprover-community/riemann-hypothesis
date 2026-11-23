module

public import Formalism.DoubleCosetMeasures.Statement
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Convex.Contractible
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.ZetaPair
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ArchimedeanSchwartz.ExpIndep
import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.MapRepApply
import Development.AutomorphicArithmetic.IntegralCasts.IsOpenStabOfMemNhds
import Formalism.LocalToGlobal.UnitaryNorms.IsUnitaryNormOf
import GroundTheory.AutomorphicForms.AutomorphicFormSpaces.Archimedean
import GroundTheory.AutomorphicForms.CuspidalDiscreteness.AltSum
import GroundTheory.AutomorphicForms.GL2.GJStandardLCuspidalGen
import GroundTheory.AutomorphicForms.GL2.GJStandardLDual
public import Mathlib.Analysis.Analytic.Uniqueness
public import Mathlib.Analysis.Calculus.FDeriv.Basic
public import Mathlib.Analysis.Complex.CauchyIntegral

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Polynomial Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.HenQ Filter
open GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.GJStandardL GroundTheory.Automorphic.GodementJacquet
open GroundTheory.Automorphic.GLnLocal GroundTheory.Automorphic.GJStandardLCuspidal UpperTheory.V UpperTheory.V.Z.Inf

attribute [-instance] Formalism.DoubleCosetMeasures.instMeasGL

private theorem far_ne {A : ℂ → ℂ} (hA : Differentiable ℂ A) (h0 : A ≠ 0) (c : ℝ) : ∃ s : ℂ, c < s.re ∧ A s ≠ 0 := by
  by_contra h
  push Not at h
  refine h0 (funext fun x => AnalyticOnNhd.eqOn_zero_of_preconnected_of_eventuallyEq_zero
    (hA.differentiableOn.analyticOnNhd isOpen_univ) isPreconnected_univ (Set.mem_univ ((c + 1 : ℝ) : ℂ)) ?_ trivial)
  filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds
    (show c < ((c + 1 : ℝ) : ℂ).re by simp)] with s hs using h s hs
