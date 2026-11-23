module

public import Mathlib.Analysis.Analytic.Order
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Data.FunLike.Fintype
public import Mathlib.NumberTheory.LSeries.DirichletContinuation
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Formalism.LandauZeroFreeBounds.ExceptionalZeroBounds.SumVonMangoldtNotCoprimeLe

@[expose] public section

open Complex Classical

noncomputable section

namespace Formalism.HermitianLattices.Ext.PrimesInProgressions

open Formalism.ZeroFreeDirichlet

def exLF {M : ℕ} [NeZero M] (χ : DirichletCharacter ℂ M) : ℂ → ℂ :=
  if χ = 1 then DirichletCharacter.LFunctionTrivChar₁ M else DirichletCharacter.LFunction χ

def exOrd {M : ℕ} [NeZero M] (χ : DirichletCharacter ℂ M) (ρ : ℂ) : ℕ :=
  analyticOrderNatAt (exLF χ) ρ

def exKer (y : ℝ) (w : ℂ) : ℂ := (y : ℂ) ^ w / (w * (w - 1))

def explicitFormulaConstant {M : ℕ} [NeZero M] (χ : DirichletCharacter ℂ M) : ℂ := -(deriv (exLF χ) 1 / exLF χ 1)

end Formalism.HermitianLattices.Ext.PrimesInProgressions
