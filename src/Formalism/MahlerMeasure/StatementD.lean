module

public import Formalism.MahlerMeasure.Statement
public import Mathlib.NumberTheory.Padics.PadicIntegers
public import Mathlib.RingTheory.Polynomial.Pochhammer
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

namespace Formalism.GM

open Finset Polynomial

noncomputable def gaussR {K : Type} [NormedField K] (ρ : NNReal) (P : K[X]) : NNReal :=
  P.support.sup (fun k => ‖P.coeff k‖₊ * ρ ^ k)

def GaussMulRad : Prop :=
  ∀ (K : Type) [NormedField K] [IsUltrametricDist K] (ρ : NNReal) (P Q : K[X]), 0 < ρ →
    gaussR ρ (P * Q) = gaussR ρ P * gaussR ρ Q

noncomputable def binK (K : Type) [Field K] (k : ℕ) : K[X] :=
  Polynomial.C (((k.factorial : K))⁻¹) * descPochhammer K k

def MahlerK : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (K : Type) [NormedField K] [NormedAlgebra ℚ_[p] K] (h k : ℕ) (t₀ : ℤ), k ≤ p ^ h →
    ∀ m : ℕ, ‖((binK K k).comp (Polynomial.C ((p : K) ^ h) * X + Polynomial.C (t₀ : K))).coeff m‖ ≤ 1

def SmithZp : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (n : ℕ) (M : Matrix (Fin n) (Fin n) ℤ_[p]),
    ∃ (U V : Matrix (Fin n) (Fin n) ℤ_[p]) (d : Fin n → ℤ_[p]),
      IsUnit U.det ∧ IsUnit V.det ∧ M = U * Matrix.diagonal d * V

noncomputable def binMatK (K : Type) [Field K] {n : ℕ} (del₀ : ℕ) (c : Fin n → Fin n → ℕ → K) :
    Matrix (Fin n) (Fin n) K[X] :=
  fun i j => ∑ k ∈ range (del₀ + 1), Polynomial.C (c i j k) * binK K k


open Classical in
def ValuationWindowLowerBound : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (K : Type) [NormedField K] [NormedAlgebra ℚ_[p] K] [IsUltrametricDist K]
    (n del₀ h : ℕ) (E : ℝ) (c : Fin n → Fin n → ℕ → K) (lead : K) (roots : Multiset K) (t₀ : ℤ)
    (U V : Matrix (Fin n) (Fin n) K) (d : Fin n → K),
    (∀ i j k, ‖c i j k‖ ≤ 1) → (∀ i j, ‖U i j‖ ≤ 1) → (∀ i j, ‖V i j‖ ≤ 1) →
    ‖U.det‖ = 1 → ‖V.det‖ = 1 → 0 ≤ E → del₀ ≤ p ^ h → lead ≠ 0 →
    (binMatK K del₀ c).det = Polynomial.C lead * (roots.map (fun ζ => X - Polynomial.C ζ)).prod →
    (binMatK K del₀ c).map (Polynomial.eval (t₀ : K)) = U * Matrix.diagonal d * V →
    ((univ.filter (fun i => ‖d i‖ ≤ (p : ℝ) ^ (-E))).card : ℝ) * E ≤
      (-Real.logb p ‖lead‖ + (roots.map (fun ζ => vmin p h ((t₀ : K) - ζ))).sum) +
        E * ((roots.filter (fun ζ => ‖(t₀ : K) - ζ‖ ≤ (p : ℝ) ^ (-(h : ℤ)))).card : ℝ)


end Formalism.GM
