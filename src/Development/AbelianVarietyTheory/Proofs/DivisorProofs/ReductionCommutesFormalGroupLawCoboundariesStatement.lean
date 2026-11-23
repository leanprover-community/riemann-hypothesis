module

public import Development.AbelianVarietyTheory.Definitions.Divisors.FormalCoboundarySmul
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ReductionCommutesFormalGroupLawCoboundaries
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

@[expose] public section

open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Katz

theorem _root_.GlobalTheory.T.reduction_commutes_formalGroupLawCoboundaries : ∀ (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] [PerfectRing k p] (d : ℕ) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) k), (∀ i, constantCoeff (μ i) = 0) → (∀ g c, Red p g c → Red p (cob2 (fun i => Katz.lift p (μ i)) g) (cob2 μ c) ∧ Red p (swap g) (swap c)) ∧ (∀ b b', Red p b b' → Red p (cob1 (fun i => Katz.lift p (μ i)) b) (cob1 μ b') ∧ RedV p (lin b) (lin b')) ∧ (∀ i, Red p (op (fun i => Katz.lift p (μ i)) x1 (op (fun i => Katz.lift p (μ i)) x2 x3) i) (op μ x1 (op μ x2 x3) i) ∧ Red p (op (fun i => Katz.lift p (μ i)) (op (fun i => Katz.lift p (μ i)) x1 x2) x3 i) (op μ (op μ x1 x2) x3 i)) ∧ ∀ (c : WittVector p k) g, g ∈ intBy p k (Fin d ⊕ Fin d) c → cob2 (fun i => Katz.lift p (μ i)) g ∈ intBy p k _ c ∧ swap g ∈ intBy p k _ c := by
  first | exact @GlobalTheory.Katz.red_coboundaries | exact GlobalTheory.Katz.red_coboundaries | (intros; apply GlobalTheory.Katz.red_coboundaries <;> assumption)
