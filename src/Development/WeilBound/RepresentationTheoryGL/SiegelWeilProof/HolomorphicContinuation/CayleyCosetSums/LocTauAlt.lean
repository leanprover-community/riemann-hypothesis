module

public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AnalyticDeterminants.SingToDiffAlt
public import Mathlib.Analysis.Normed.Algebra.Exponential
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

open MeasureTheory Matrix Set Filter Topology
open scoped NNReal

namespace PositivityTheory.Rg.Sw.HSt

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs

variable {n : ℕ}

def fz (m : ℕ) (e : ℤ) (z : ℂ) (x : M2 n) : ℂ :=
  x.det ^ e * (u1 x).det ^ (-(m : ℤ)) * ((u1 x).det * (ub1 x).det) ^ (-z)

def sig (X : M2 n) : M2 n := -((JJ n)⁻¹ * Xᴴ * JJ n)

def rC (Z : M2 n) (F : M2 n → ℂ) (x : M2 n) : ℂ :=
  deriv (fun t : ℝ => F (x * NormedSpace.exp ((t : ℂ) • ((1 / 2 : ℂ) • (Z + sig Z))))) 0 +
    Complex.I * deriv (fun t : ℝ => F (x * NormedSpace.exp ((t : ℂ) • ((1 / (2 * Complex.I)) • (Z - sig Z))))) 0

def lowQ (Q : Matrix (Fin n) (Fin n) ℂ) : M2 n := mX 1 Q 0 1 - 1

def tOp {Kg : Type} [MeasurableSpace Kg] (μ : Measure Kg) (ι : Kg → M2 n) (ρ : Kg → ℂ)
    (ψ : (Fin n → Fin n → ℝ) → ℂ) (a b : M2 n) (F : M2 n → ℂ) (x : M2 n) : ℂ :=
  ∫ k, ρ k * (∫ t : Fin n → Fin n → ℝ, F (x * ι k * a * nU (herm t) * b) * ψ t) ∂μ

def LocTau : Prop :=
  ∀ (n m : ℕ) (e : ℤ), m < n → ∀ (Kg : Type) [Group Kg] [TopologicalSpace Kg] [IsTopologicalGroup Kg] [CompactSpace Kg]
    [MeasurableSpace Kg] [BorelSpace Kg] (μ : Measure Kg) [μ.IsHaarMeasure] (ι : Kg →* M2 n), Continuous ι →
    (∀ g, InK g ↔ ∃ k, ι k = g) → ∀ Q : Matrix (Fin n) (Fin n) ℂ,
    ∃ (N : ℕ) (ρ : Fin N → Kg → ℂ) (ψ : Fin N → (Fin n → Fin n → ℝ) → ℂ) (a b : Fin N → M2 n) (D : ℂ → ℂ)
      (M : Fin N → ℂ → ℂ), (∀ l, Continuous (ρ l)) ∧ (∀ l, IsSingTest (ψ l)) ∧ (∀ l, InG (a l) ∧ InG (b l)) ∧
      Differentiable ℂ D ∧ D 0 ≠ 0 ∧ (∀ l, Differentiable ℂ (M l)) ∧
      ∀ (z : ℂ) (x : M2 n), InG x →
        D z * rC (lowQ Q) (fz m e z) x = ∑ l, M l z * tOp μ ι (ρ l) (ψ l) (a l) (b l) (fz m e z) x

end PositivityTheory.Rg.Sw.HSt
