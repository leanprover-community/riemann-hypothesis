module

public import Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinContinuation.StripEntire
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

namespace PositivityTheory.RgEis

def Twist : Prop :=
  ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G]
    (Γ K S P P' : Subgroup G) (c c₀ : G → ℂ) (η η' β ξ : G → ℝ) (N : ℝ), IsCompact (K : Set G) → IsCh Γ ⊤ c₀ →
    IsPar Γ K S c → IsPar Γ K P c → IsPar Γ K P' c →
    ((AllRep K fun ρ => HasWall Γ K P P' c η η' β ρ) → AllRep K fun ρ => HasWall Γ K P P' (c * c₀) η η' β ρ) ∧
    ((AllRep K fun ρ => HasFirst Γ K S P P' c η η' β ρ) → AllRep K fun ρ => HasFirst Γ K S P P' (c * c₀) η η' β ρ) ∧
    ((AllRep K fun ρ => HasLast Γ K S P P' c η η' β ξ N ρ) → AllRep K fun ρ => HasLast Γ K S P P' (c * c₀) η η' β ξ N ρ)

def Scale : Prop := ForRep fun {G} _ _ {_W} _ _ K ρ => ∀ (Γ P P' : Subgroup G) (c : G → ℂ) (η η' β l : G → ℝ) (s : ℝ), 0 < s →
  IsHt Γ K ⊤ l → HasWall Γ K P P' c η η' β ρ →
  HasWall Γ K P P' c (fun g => s * (η g + l g)) (fun g => s * (η' g - l g)) β ρ

end PositivityTheory.RgEis
