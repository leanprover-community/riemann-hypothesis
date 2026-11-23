module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.UnfoldingConstantsPos
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.RealisedChainTorusEq

@[expose] public section

noncomputable section

namespace GlobalTheory.Core.Rk

open Formalism.BasicNotions Formalism.MainNotions.S
open scoped InnerProductSpace

variable (D : D7) (u : D.what₂.Word)

def TwoTerm (A x : ℝ) : Prop := hsDev D u ≤ A * (d0 D u : ℝ) ^ 2 / D.what₂.Dstar + x * (d0 D u : ℝ)

def mfL (L : ℝ) : ℝ := (D.R.m : ℝ) ^ 5 * D.R.f * L

def kfk : ℝ := (D.R.k : ℝ) * D.R.f * Real.log D.R.k

def SDiag (L C : ℝ) : Prop :=
  TwoTerm D u (4 * (Real.exp (C * mfL D L) + 1)) (4 * Real.exp (-(kfk D / 2)) + 2 * Real.exp (-kfk D))

def Small (L C : ℝ) : Prop := (d0 D u : ℝ) ≤ D.what₂.Dstar * Real.exp (-(2 * C * mfL D L))

def eDiag (L C : ℝ) : ℝ := 8 * Real.exp (-(C * mfL D L)) + 6 * Real.exp (-(kfk D / 2))

def RankMu : Prop :=
  (d0 D u : ℝ) = ((D.mem u).A.duStar : ℝ) * (((D.mem u).A.T : ℝ) ^ D.R.k - 1) ^ D.R.f

def cK : ℝ := (c0 D.s u * c0 D.s u) ^ (-(1 / 2 : ℝ))

namespace Pts

variable (F : Pts)

end Pts

end GlobalTheory.Core.Rk

end
