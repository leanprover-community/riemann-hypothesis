module

public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LayerProd
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
import Mathlib.Tactic.Linter.HaveILetI
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

@[expose] public section

open MeasureTheory NumberField
open scoped ENNReal

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.NearNonzeroTerms

open Formalism.MainNotions.S GlobalTheory.Count

variable (B : RowsAut)

def moderate (q : ℕ) (b : ℝ) : Set B.I.GA := {x | x ∈ B.fund ∧ tauStar B q b ≤ least B.I x}

def nearNe (d : InfinitePlace B.I.F → ℝ) (x : B.I.GA) : Set B.I.GA :=
  {γ | IsNear B d (epN B) x γ ∧ γ ≠ 1}

def nearAbs (d : InfinitePlace B.I.F → ℝ) (x : B.I.GA) : ℝ≥0∞ :=
  ∑' γ : nearNe B d x, ‖phe B d (x⁻¹ * γ.1 * x)‖ₑ

def nearBound (d : InfinitePlace B.I.F → ℝ) : ℝ :=
  Real.exp (-(1 / 4 * (B.I.n : ℝ) * (B.I.f : ℝ) * Real.log (B.I.n : ℝ))) * mainTerm B d

def NearModerate : Prop :=
  ∀ Cg : ℝ, 0 ≤ Cg → ∃ n₀ : ℕ, ∀ (B : RowsAut) (d : InfinitePlace B.I.F → ℝ) (p q : ℕ) (b : ℝ),
    1 ≤ q → CountHyp B Cg n₀ d p q b →
      ∫⁻ x in moderate B q b, nearAbs B d x ∂(B.I.muA B.μf) ≤ ENNReal.ofReal (nearBound B d)

theorem nearAbs_eq_zero (d : InfinitePlace B.I.F → ℝ) (x : B.I.GA)
    (h : ∀ γ, IsNear B d (epN B) x γ → γ = 1) : nearAbs B d x = 0 := by
  haveI : IsEmpty (nearNe B d x) := ⟨fun γ => γ.2.2 (h γ.1 γ.2.1)⟩
  simp [nearAbs]

end GlobalTheory.IndefiniteRowSideFullHecke.NearNonzeroTerms
