module

public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.DerivativeVacuumDilationsAlt
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

@[expose] public section

noncomputable section

open MeasureTheory Matrix Set Filter Topology

namespace PositivityTheory.Rg.Sw.AbsSt

open PositivityTheory.Rg.Sw

variable {n : ℕ}

def Ac (X : Fin n → ℝ) (z : ℂ) : M2 n :=
  fromBlocks (diagonal fun j => Complex.exp (z * X j)) 0 0 (diagonal fun j => Complex.exp (-(z * X j)))

def holomorphicSectionExtension (p q : ℕ) (e : ℤ) (X : Fin n → ℝ) (h : GR n) (z : ℂ) : ℂ :=
  (mR h).det ^ e * (u1 (mR h * Ac X z)).det ^ (-(p : ℤ)) * (u2 (mR h * Ac X z)).det ^ (-(q : ℤ))

def HelpA : Prop :=
  (∀ (n : ℕ) (X : Fin n → ℝ), ∃ a : ℝ → GR n, ∀ s, IsDil X s (a s)) ∧
  (∀ (n : ℕ) (X : Fin n → ℝ) (s : ℝ) (a a' : GR n), IsDil X s a → IsDil X s a' → a = a') ∧
  (∀ n : ℕ, IsCompact (univ : Set (KR n))) ∧
  (∀ (n : ℕ) (h : GR n), (u1 (mR h)).det ≠ 0 ∧ (u2 (mR h)).det ≠ 0) ∧
  (∀ (n p q : ℕ) (e : ℤ) (X : Fin n → ℝ) (a : ℝ → GR n), (∀ s, IsDil X s (a s)) → ∀ (h : GR n) (s : ℝ),
    holomorphicSectionExtension p q e X h s = F0 p q e (h * a s)) ∧
  (∀ (n p q : ℕ) (e : ℤ) (X : Fin n → ℝ) (S : Set (GR n)), IsCompact S → ∃ V : Set ℂ, IsOpen V ∧ (∀ s : ℝ, (s : ℂ) ∈ V) ∧
    ContinuousOn (fun y : GR n × ℂ => holomorphicSectionExtension p q e X y.1 y.2) (S ×ˢ V) ∧ ∀ h ∈ S, DifferentiableOn ℂ (holomorphicSectionExtension p q e X h) V) ∧
  (∀ (n p q : ℕ) (e : ℤ), Continuous (F0 (n := n) p q e) ∧ ∀ k : GR n, k ∈ KR n → F0 p q e k ≠ 0)

def HelpC : Prop :=
  (∀ (f : ℂ → ℂ) (V : Set ℂ), IsOpen V → (∀ s : ℝ, (s : ℂ) ∈ V) → DifferentiableOn ℂ f V →
    ∀ (r : ℕ) (s : ℝ), iteratedDeriv r (fun t : ℝ => f t) s = iteratedDeriv r f s) ∧
  (∀ (f : ℂ → ℂ) (V : Set ℂ), IsOpen V → (∀ s : ℝ, (s : ℂ) ∈ V) → DifferentiableOn ℂ f V →
    (∀ r : ℕ, iteratedDeriv r f 0 = 0) → ∀ s : ℝ, f s = 0)

end PositivityTheory.Rg.Sw.AbsSt
