module

public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
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

open MeasureTheory

namespace UpperTheory.Lit.Cusp

variable {G : Type} [Group G] [TopologicalSpace G]

def conv [MeasurableSpace G] (μ : Measure G) (f h : G → ℂ) (x : G) : ℂ := ∫ g, f g * h (g⁻¹ * x) ∂μ

structure IsRay (N : Set G) (a : ℝ → G) (H : G → ℝ) : Prop where

  cont : Continuous a

  add : ∀ s t, a (s + t) = a s * a t

  norm : ∀ t, ∀ m ∈ N, (a t)⁻¹ * m * a t ∈ N

  contH : Continuous H

  inv : ∀ g, ∀ m ∈ N, H (g * m) = H g

  move : ∀ g t, H (g * a t) = H g + t

  bdd : ∀ D : Set G, IsCompact D → ∃ c : ℝ, ∀ g ∈ D, ∀ x, |H (g⁻¹ * x) - H x| ≤ c

  cpt : ∃ C : Set G, IsCompact C ∧ ∀ x, ∃ k ∈ C, ∀ t, ∃ m ∈ N, k * a t * k⁻¹ * x = x * a t * m

def IsEig (N : Set G) (a : ℝ → G) (s C : ℝ) (h : G → ℂ) : Prop :=
  Continuous h ∧ (∀ g, ‖h g‖ ≤ C) ∧ (∀ g, ∀ m ∈ N, h (g * m) = h g) ∧
    ∀ g t, h (g * a t) = Complex.exp ((s * t : ℝ) * Complex.I) * h g

def OpLe [MeasurableSpace G] (μ : Measure G) (N : Set G) (a : ℝ → G) (f : G → ℂ) (s r : ℝ) : Prop :=
  ∀ C h, IsEig N a s C h → ∀ x, ‖conv μ f h x‖ ≤ r * C

def Kills [MeasurableSpace G] (μ : Measure G) (N : Set G) (a : ℝ → G) (f : G → ℂ) : Prop :=
  ∀ s C h, IsEig N a s C h → ∀ x, conv μ f h x = 0

def IsBand (N : Set G) (H : G → ℝ) (h : G → ℂ) : Prop :=
  Continuous h ∧ (∃ C, ∀ g, ‖h g‖ ≤ C) ∧ (∀ g, ∀ m ∈ N, h (g * m) = h g) ∧ ∃ R : ℝ, ∀ g, h g ≠ 0 → |H g| ≤ R

end UpperTheory.Lit.Cusp

end
