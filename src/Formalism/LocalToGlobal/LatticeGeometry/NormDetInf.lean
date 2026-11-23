module

public import Formalism.LocalToGlobal.LatticeGeometry.DegFlLApply
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

open Formalism.BasicNotions

namespace Formalism.L2.Geo

structure CxPkg (Tau : Type) [Fintype Tau] (N j : ℕ) (Comp : Type) [Fintype Comp] where

  Γ : Comp → Subgroup (Tau → GL (Fin j ⊕ Fin (N - j)) ℂ)
  Γ_le : ∀ c, Γ c ≤ Formalism.DegreeFormula.UpqI Tau j (N - j)

  volC : Comp → ℝ
  volC_pos : ∀ c, 0 < volC c

  rfn : (Σ c, XCc Tau j (N - j) (Γ c)) → ℝ
  rfn_ge : ∀ z, Real.exp 1 ≤ rfn z

  hLo : (Σ c, XCc Tau j (N - j) (Γ c)) → ℝ
  hUp : (Σ c, XCc Tau j (N - j) (Γ c)) → ℝ
  hLo_le : ∀ z, 0 < hLo z ∧ hLo z ≤ hUp z

  connN : (Σ c, XCc Tau j (N - j) (Γ c)) → ℝ
  curvN : (Σ c, XCc Tau j (N - j) (Γ c)) → ℝ

  normDetInf : Tau → (Σ c, XCc Tau j (N - j) (Γ c)) → ℝ

namespace CxPkg

variable {Tau : Type} [Fintype Tau] {N j : ℕ} {Comp : Type} [Fintype Comp] (X : CxPkg Tau N j Comp)

def XC : Type := Σ c, XCc Tau j (N - j) (X.Γ c)

def compOf : X.XC → Comp := Sigma.fst

def vol : ℝ := ∑ c, X.volC c

def chern : MvPolynomial (DV.Rt Tau N) ℝ →ₗ[ℝ] ℝ := chernOf Tau N X.vol

end CxPkg

end Formalism.L2.Geo
