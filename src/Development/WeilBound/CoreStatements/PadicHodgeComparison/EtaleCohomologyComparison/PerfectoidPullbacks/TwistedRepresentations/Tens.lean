module

public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.InstAddCommGroup
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

open TensorProduct

namespace CrystallineSemistableComparison.Tw

variable {W : Type} [CommRing W]

structure LSeq (l : ℕ) (S S' : Sys.{1} W) where
  ρ : ∀ c b, S.M c →ₗ[W] S.M b
  ν : ∀ a c, S.M a →ₗ[W] S.M c
  δ : ∀ b a, S.M b →ₗ[W] S'.M a
  kill : ∀ n (x : S.M n), ((l : W) ^ n) • x = 0
  ρ_self : ∀ c x, ρ c c x = x
  ρ_succ : ∀ c b, b ≤ c → ∀ x, ρ (c + 1) b x = ρ c b (S.r c x)
  ν_ρ : ∀ a c, a ≤ c → ∀ x, ν a c (ρ c a x) = ((l : W) ^ (c - a)) • x
  ν_r : ∀ a c, a ≤ c → ∀ y, S.r c (ν (a + 1) (c + 1) y) = ν a c (S.r a y)
  ex₁ : ∀ a b c, c = a + b → ∀ x, ρ c b x = 0 → ∃ y, ν a c y = x
  δ_r : ∀ b a x, S'.r a (δ b (a + 1) x) = δ b a x
  ex₂ : ∀ a b c, c = a + b → ∀ x, δ b a x = 0 → ∃ y, ρ c b y = x

def pr (S : Sys.{1} W) (n : ℕ) : S.lim →ₗ[W] S.M n := (LinearMap.proj n).comp S.lim.subtype

def tens (A : Type) [CommRing A] [Algebra W A] (S : Sys.{1} W) : Sys.{1} A where
  M n := A ⊗[W] S.M n
  r n := (S.r n).baseChange A

end CrystallineSemistableComparison.Tw

end
