module

public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StatementsCurrent
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial Filter Topology ComplexSets

noncomputable section

variable {n : ℕ}

def DivisorRegularAt (J : Ideal (MvPolynomial (Fin n) ℂ)) (u : Fin n → ℂ) (d : ℕ) (q : Fin n → ℂ) : Prop :=
  ∃ (A : (Fin n → ℂ) →L[ℂ] (Fin d → ℂ)) (O : Set (Fin d → ℂ)) (V : Set (Fin n → ℂ))
    (g : (Fin d → ℂ) → Fin n → ℂ), IsOpen O ∧ IsOpen V ∧ q ∈ V ∧ AnalyticOnNhd ℂ g O ∧
      (∀ y ∈ O, A (g y) = y) ∧ zeroSet J ∩ {x | linEval u x = 0} ∩ V = g '' O

def NormalDivisorChartAt {J : Ideal (MvPolynomial (Fin n) ℂ)} (M : IndefiniteRowSideFullHecke.ComplexSets.NormalModel J)
    (u : Fin n → ℂ) (d : ℕ) (q : Fin n → ℂ) : Prop :=
  ∀ w ∈ IndefiniteRowSideFullHecke.ComplexSets.zeroSetIn M.ideal, IndefiniteRowSideFullHecke.ComplexSets.firstCoords w = q →
    ∃ (r : ℝ) (φ : (Fin (d + 1) → ℂ) → Fin n ⊕ Fin M.m → ℂ) (k : ℕ), 0 < r ∧
      DifferentiableOn ℂ φ (Metric.ball 0 r) ∧ Set.InjOn φ (Metric.ball 0 r) ∧ φ 0 = w ∧
      Set.MapsTo φ (Metric.ball 0 r) (IndefiniteRowSideFullHecke.ComplexSets.zeroSetIn M.ideal) ∧
      (∀ s : ℝ, 0 < s → ∃ U ∈ 𝓝 w, IndefiniteRowSideFullHecke.ComplexSets.zeroSetIn M.ideal ∩ U ⊆ φ '' Metric.ball 0 s) ∧
      VanishesToOrder (fun t => linEval u (IndefiniteRowSideFullHecke.ComplexSets.firstCoords (φ t))) r k ∧
      ∀ v : Fin (d + 1) → ℂ, v 0 = 0 →
        fderiv ℂ (fun t => IndefiniteRowSideFullHecke.ComplexSets.firstCoords (φ t)) 0 v = 0 → v = 0

def NormalDoublePointsOnDivisor {J : Ideal (MvPolynomial (Fin n) ℂ)} (M : IndefiniteRowSideFullHecke.ComplexSets.NormalModel J)
    (u : Fin n → ℂ) (q : Fin n → ℂ) : Prop :=
  ∃ N ∈ 𝓝 q, ∀ w ∈ IndefiniteRowSideFullHecke.ComplexSets.zeroSetIn M.ideal, ∀ w' ∈ IndefiniteRowSideFullHecke.ComplexSets.zeroSetIn M.ideal,
    IndefiniteRowSideFullHecke.ComplexSets.firstCoords w = IndefiniteRowSideFullHecke.ComplexSets.firstCoords w' →
      IndefiniteRowSideFullHecke.ComplexSets.firstCoords w ∈ N → w ≠ w' → linEval u (IndefiniteRowSideFullHecke.ComplexSets.firstCoords w) = 0

end

end GroundTheory.Heights₂.Heights
