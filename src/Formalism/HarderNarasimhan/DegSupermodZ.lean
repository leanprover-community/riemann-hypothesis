module

public import Formalism.HarderNarasimhan.Statement
public import Formalism.LatticeSlopes.CovolAntiSameRank
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open Module Submodule

noncomputable section

namespace Formalism.HN

def DegSupermodZ : Prop :=
  ∀ (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (L A B : Submodule ℤ E), DiscreteTopology L → A ≤ L → B ≤ L →
    Formalism.F.rk (A ⊔ B) + Formalism.F.rk (A ⊓ B) = Formalism.F.rk A + Formalism.F.rk B ∧
    Formalism.F.deg A + Formalism.F.deg B ≤ Formalism.F.deg (A ⊔ B) + Formalism.F.deg (A ⊓ B)

def SatR : Prop :=
  ∀ (R V E : Type*) [Ring R] [AddCommGroup V] [Module R V] [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] (ρ : V →+ E) (L N : Submodule R V),
    IsLat ρ L → N ≤ L →
    ∃ N' : Submodule R V, N ≤ N' ∧ N' ≤ L ∧ zl ρ N' = Formalism.F.satur (zl ρ L) (zl ρ N)

def FinSup : Prop :=
  ∀ (R V E : Type*) [Ring R] [AddCommGroup V] [Module R V] [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] (ρ : V →+ E) (L : Submodule R V)
    (S : Set (Submodule R V)), IsLat ρ L → (∀ N ∈ S, N ≤ L) →
    ∃ t : Finset (Submodule R V), (↑t : Set (Submodule R V)) ⊆ S ∧ sSup S = t.sup id

def SatBasic : Prop :=
  ∀ (R V E : Type*) [Ring R] [AddCommGroup V] [Module R V] [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] (ρ : V →+ E) (L : Submodule R V),
    IsLat ρ L →
    (∀ N : Submodule R V, N ≤ L → IsLat ρ N) ∧
    (∀ A B : Submodule R V, A ≤ B → B ≤ L → rk ρ A ≤ rk ρ B ∧ (rk ρ A = rk ρ B → deg ρ A ≤ deg ρ B)) ∧
    (∀ S N : Submodule R V, IsSat ρ L S → S ≤ N → N ≤ L → rk ρ N = rk ρ S → N = S) ∧
    (∀ N : Submodule R V, N ≤ L → (rk ρ N = 0 ↔ N = ⊥)) ∧
    deg ρ (⊥ : Submodule R V) = 0 ∧ IsSat ρ L ⊥ ∧ IsSat ρ L L ∧
    (∀ S : Submodule R V, IsSat ρ L S →
      Formalism.F.rk (Formalism.F.quot (zl ρ L) (zl ρ S)) = rk ρ L - rk ρ S ∧
      rk ρ S ≤ rk ρ L ∧
      Formalism.F.deg (Formalism.F.quot (zl ρ L) (zl ρ S)) = deg ρ L - deg ρ S)

def RatioMax : Prop :=
  ∀ (R V E : Type*) [Ring R] [AddCommGroup V] [Module R V] [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] (ρ : V →+ E) (L S : Submodule R V),
    IsLat ρ L → IsSat ρ L S → S ≠ L →
    ∃ N : Submodule R V, S < N ∧ IsSat ρ L N ∧
      ∀ N' : Submodule R V, S < N' → N' ≤ L →
        (deg ρ N' - deg ρ S) * ((rk ρ N : ℝ) - rk ρ S) ≤
          (deg ρ N - deg ρ S) * ((rk ρ N' : ℝ) - rk ρ S)

end Formalism.HN
