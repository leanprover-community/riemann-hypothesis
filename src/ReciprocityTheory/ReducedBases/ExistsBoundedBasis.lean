module

public import ReciprocityTheory.ReducedBases.LatDefs
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
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

namespace ReciprocityTheory.ReducedBases.T2

open ReciprocityTheory.ReducedBases Matrix

def C1 (d : ℕ) : ℝ := (d : ℝ) * (3 / 2 : ℝ) ^ d * (2 : ℝ) ^ ((d : ℝ) / 2 - 1)

def BilinBoundedBasis {d : ℕ} (A : Matrix (Fin d) (Fin d) ℝ) (e : Module.Basis (Fin d) ℤ (Fin d → ℤ)) : Prop :=
  ∀ (i : Fin d) (μ : Fin d → ℤ), |polar A (e i) μ| ≤ (d : ℝ) * (2 : ℝ) ^ ((d : ℝ) / 2) * polar A μ μ

def CoordBoundedOnMin {d : ℕ} (A : Matrix (Fin d) (Fin d) ℝ) (e : Module.Basis (Fin d) ℤ (Fin d → ℤ)) : Prop :=
  ∀ (N : ℤ), 1 ≤ N → ∀ α : Fin d → ℤ, IsMinInClass (Q A) N α →
    ∀ i : Fin d, |((e.repr α i : ℤ) : ℝ)| ≤ C1 d * (N : ℝ)

def ExistsBoundedBasis : Prop :=
  ∀ (d : ℕ) (A : Matrix (Fin d) (Fin d) ℝ), A.PosDef →
    ∃ e : Module.Basis (Fin d) ℤ (Fin d → ℤ), BilinBoundedBasis A e ∧ CoordBoundedOnMin A e

end ReciprocityTheory.ReducedBases.T2

end
