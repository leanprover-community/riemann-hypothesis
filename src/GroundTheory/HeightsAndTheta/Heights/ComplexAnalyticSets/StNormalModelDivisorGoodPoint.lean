module

public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Statements
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StNormalModel
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
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Statements

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial ComplexSets

noncomputable section

def NormalModelDivisorGoodPoint {n : ℕ} {J : Ideal (MvPolynomial (Fin n) ℂ)}
    (M : IndefiniteRowSideFullHecke.ComplexSets.NormalModel J) (u : Fin n → ℂ) (d : ℕ) (w : Fin n ⊕ Fin M.m → ℂ) : Prop :=
  w ∈ IndefiniteRowSideFullHecke.ComplexSets.zeroSetIn M.ideal ∧
  ∃ (c : ℕ) (f : Fin c → MvPolynomial (Fin n ⊕ Fin M.m) ℂ) (h g a b : MvPolynomial (Fin n ⊕ Fin M.m) ℂ) (k : ℕ),
    c + (d + 1) = n + M.m ∧ (∀ j, f j ∈ M.ideal) ∧
    eval w h ≠ 0 ∧ (∀ p ∈ M.ideal, ∃ e : ℕ, h ^ e * p ∈ Ideal.span (Set.range f)) ∧
    eval w g = 0 ∧
    LinearIndependent ℂ (Fin.cons (fun s ↦ eval w (pderiv s g)) (fun j s ↦ eval w (pderiv s (f j))) :
      Fin (c + 1) → Fin n ⊕ Fin M.m → ℂ) ∧
    0 < k ∧ eval w a ≠ 0 ∧ eval w b ≠ 0 ∧
    b * rename (Sum.inl : Fin n → Fin n ⊕ Fin M.m) (linForm u) - a * g ^ k ∈ M.ideal ∧
    ∀ v : Fin n ⊕ Fin M.m → ℂ, (∀ i : Fin n, v (Sum.inl i) = 0) →
      ∑ s, eval w (pderiv s g) * v s = 0 → (∀ j, ∑ s, eval w (pderiv s (f j)) * v s = 0) → v = 0

end

end GroundTheory.Heights₂.Heights
