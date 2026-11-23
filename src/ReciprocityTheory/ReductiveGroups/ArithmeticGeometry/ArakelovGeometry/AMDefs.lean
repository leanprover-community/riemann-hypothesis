module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ArithmeticHilbertSamuelLowerBound
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
import ReciprocityTheory.GeometryOfNumbers.PluriharmonicAnalysis.BergmanDefs

@[expose] public section

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.GeometryOfNumbersTheory MvPolynomial MeasureTheory

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

def unitDeg [DecidableEq K] (k₀ : K) : K → ℤ := fun k => if k = k₀ then 1 else 0

def blockDeg [DecidableEq K] (k₀ : K) (n : ℕ) : K → ℕ := fun k => if k = k₀ then n else 0

variable {Ω : Type} [Field Ω] [CharZero Ω]

def IsSecBasisM [DecidableEq K] (y : (Σ k, ι k) → Ω) (k₀ : K) (n : ℕ) {r : ℕ}
    (b : Fin r → MvPolynomial (Σ k, ι k) ℚ) : Prop :=
  (∀ j, ∃ f : MRing ι, IsMultiHomog f (blockDeg k₀ n) ∧ b j = map (Int.castRingHom ℚ) f) ∧
    LinearIndependent ℤ (fun j => aeval y (b j)) ∧
    (Submodule.span ℤ (Set.range fun j => aeval y (b j))).toAddSubgroup = secM y (blockDeg k₀ n)


end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
