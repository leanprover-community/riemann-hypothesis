module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftWeightCombinatorialDataULeUZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftWeightRhoNonThickPlaceCentreWidth
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.SumExpSt

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links GlobalTheory.ExpTie GlobalTheory.ExpTie.Lift

theorem _root_.GlobalTheory.T.liftWeightRho_nonThickPlace_centre_width : ∀ {D : Formalism.BasicNotions.D7} (L : Formalism.BasicNotions.SizeData₂ D) (P5 : Formalism.BasicNotions.ParameterChoice' D L) (j : Fin D.R.m) (τ : D.what₂.Tau), GlobalTheory.ExpTie.Lift.ValsAt L j τ → τ ∉ (GlobalTheory.ExpTie.Lift.wts L j).T2 → ((GlobalTheory.ExpTie.parOf L j).Top ((GlobalTheory.ExpTie.Lift.wts L j).e τ) ∧ ((GlobalTheory.ExpTie.Lift.wts L j).width (GlobalTheory.ExpTie.parOf L j) τ : ℝ) ≤ (GlobalTheory.ExpTie.parOf L j).S + (GlobalTheory.ExpTie.parOf L j).b' * (1 + 1 / (GlobalTheory.ExpTie.parOf L j).x + 1 / (GlobalTheory.ExpTie.parOf L j).x ^ 2) + (GlobalTheory.ExpTie.parOf L j).η + (((GlobalTheory.ExpTie.parOf L j).t : ℝ) - 1) / 2) ∨ ((GlobalTheory.ExpTie.parOf L j).Thin ((GlobalTheory.ExpTie.Lift.wts L j).e τ) ∧ ((GlobalTheory.ExpTie.Lift.wts L j).width (GlobalTheory.ExpTie.parOf L j) τ : ℝ) ≤ (GlobalTheory.ExpTie.parOf L j).S + (GlobalTheory.ExpTie.parOf L j).w'' + (GlobalTheory.ExpTie.parOf L j).η + (((GlobalTheory.ExpTie.parOf L j).t : ℝ) - 1) / 2) := by
  exact @GlobalTheory.ExpTie.Lift.other_of_not_thick
