module

public import Mathlib.LinearAlgebra.Matrix.PosDef
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.AR.IntegralModuleBases

open Module Matrix
open scoped NumberField

def gramConst (d : ℕ) : ℝ := 2 ^ (d * (d - 1))

def RedGramStatement : Prop :=
  ∀ (d : ℕ) (A : Matrix (Fin d) (Fin d) ℝ) (m D : ℝ), A.PosDef → 0 < m →
    (∀ x : Fin d → ℤ, x ≠ 0 → m ≤ (fun i => (x i : ℝ)) ⬝ᵥ (A *ᵥ fun i => (x i : ℝ))) →
    A.det ≤ D →
    ∃ e : Module.Basis (Fin d) ℤ (Fin d → ℤ),
      (∀ i, (fun l => (e i l : ℝ)) ⬝ᵥ (A *ᵥ fun l => (e i l : ℝ)) ≤
        2 ^ (d * (d - 1)) * D / m ^ (d - 1)) ∧
      ∀ (x : Fin d → ℤ) (i : Fin d), ((e.repr x i : ℤ) : ℝ) ^ 2 ≤
        9 ^ d * ((fun l => (x l : ℝ)) ⬝ᵥ (A *ᵥ fun l => (x l : ℝ))) / m

end ReciprocityTheory.ChartRestriction.G.AR.IntegralModuleBases

end
