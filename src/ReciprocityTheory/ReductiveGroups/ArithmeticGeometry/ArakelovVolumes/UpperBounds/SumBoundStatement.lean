module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.LiftFactorization
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

namespace ReciprocityTheory.ChartRestriction.G.AR.Up

open ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ContDiff ENNReal Matrix ComplexOrder

noncomputable section

def Jf (p q : ℕ) : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ :=
  Matrix.fromBlocks 1 0 0 (-1)

def IsUpq {p q : ℕ} (g : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) : Prop := gᴴ * Jf p q * g = Jf p q

def mob {p q : ℕ} (g : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) (Z : Matrix (Fin p) (Fin q) ℂ) :
    Matrix (Fin p) (Fin q) ℂ :=
  (g.toBlocks₁₁ * Z + g.toBlocks₁₂) * (g.toBlocks₂₁ * Z + g.toBlocks₂₂)⁻¹

def dpow {p q : ℕ} (Z : Matrix (Fin p) (Fin q) ℂ) (s : ℝ) : ℝ := (1 - Z * Zᴴ).det.re ^ s

def SumBoundStatement : Prop :=
  ∀ (f p q : ℕ) (s : ℝ), 2 * (f : ℝ) * ((p + q : ℕ) : ℝ) ^ 2 < s →
    ∀ (Γ : Subgroup (Fin f → GL (Fin p ⊕ Fin q) ℂ)), DiscreteTopology Γ →
    (∀ γ ∈ Γ, ∀ k, IsUpq ((γ k : GL (Fin p ⊕ Fin q) ℂ) : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ)) →
    ∃ C : ℝ≥0∞, C < ⊤ ∧ ∀ v ∈ Dset f p q,
      ∑' γ : Γ, ENNReal.ofReal (∏ k, dpow (mob ((γ.1 k : GL (Fin p ⊕ Fin q) ℂ) :
        Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) (Zof v k)) s) ≤ C

end

end ReciprocityTheory.ChartRestriction.G.AR.Up
