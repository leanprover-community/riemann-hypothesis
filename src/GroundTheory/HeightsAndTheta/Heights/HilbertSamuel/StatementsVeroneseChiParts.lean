module

public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsSecondVeroneseParts
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.CSandwichStA
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.GeometryOfNumbersTheory MeasureTheory

noncomputable section

open Veronese

def VeroneseMonoBasis.Statement : Prop :=
  ∀ D n : ℕ, ∃ b : Fin (Finset.Nat.antidiagonalTuple (D + 1) (2 * n)).card → MvPolynomial (Ix (Idx D)) ℚ,
    IsSecBasis (Veronese.x D) n b ∧
      ∀ k, aeval (Veronese.x D) (b k) = ∏ i, Veronese.t D i ^ adtEnum D (2 * n) k i

def VeroneseGramMono.Statement : Prop :=
  ∀ (D n r : ℕ) (b : Fin r → MvPolynomial (Ix (Idx D)) ℚ)
    (A : Matrix (Fin r) (Fin (Finset.Nat.antidiagonalTuple (D + 1) (2 * n)).card) ℤ),
    (∀ k, aeval (Veronese.x D) (b k) =
      ∑ l, (A k l : Veronese.Fld D) * ∏ i, Veronese.t D i ^ adtEnum D (2 * n) l i) →
    Veronese.gram D n b = A.map (Int.cast : ℤ → ℝ) *
      Matrix.diagonal (fun l => monoNormSq (adtEnum D (2 * n) l)) * (A.map (Int.cast : ℤ → ℝ)).transpose

theorem adtEnum_zero_eq (D : ℕ) (l : Fin (Finset.Nat.antidiagonalTuple (D + 1) 0).card) :
    adtEnum D 0 l = 0 := by
  have h := Finset.Nat.mem_antidiagonalTuple.mp
    (((Finset.Nat.antidiagonalTuple (D + 1) 0).equivFin.symm l).2)
  funext i
  exact (Finset.sum_eq_zero_iff.mp h) i (Finset.mem_univ i)

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
