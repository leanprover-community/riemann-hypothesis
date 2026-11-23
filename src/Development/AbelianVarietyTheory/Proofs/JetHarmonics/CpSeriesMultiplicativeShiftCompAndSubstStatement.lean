module

public import Development.AbelianVarietyTheory.Definitions.Jets.CmLatticeCommutatorPairingPowEqOneOfGoodLift
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.CpSeriesMultiplicativeShiftCompAndSubst
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

open PowerSeries GlobalTheory.MomOne
open scoped ComplexConjugate BigOperators Topology

theorem _root_.GlobalTheory.T.cpSeriesMultiplicativeShift_comp_and_subst : ∀ (q : ℕ) [Fact q.Prime], (∀ (ζ ξ : ℂ_[q]) (f : ℂ_[q]⟦X⟧), ‖ζ - 1‖ < 1 → ‖ξ - 1‖ < 1 → Bdd f → shiftS ζ (shiftS ξ f) = shiftS (ζ * ξ) f) ∧ ∀ (ζ : ℂ_[q]) (n k : ℕ) (a : ℤ_[q]) (f : ℂ_[q]⟦X⟧), ζ ^ (q ^ n) = 1 → ‖a - (k : ℤ_[q])‖ ≤ (q : ℝ) ^ (-(n : ℤ)) → Bdd f → ‖ζ - 1‖ < 1 ∧ shiftS ζ (f.subst (mulS a : ℂ_[q]⟦X⟧)) = (shiftS (ζ ^ k) f).subst (mulS a : ℂ_[q]⟦X⟧) := by
  first | exact @GlobalTheory.MomOne.ShiftComp.main | exact GlobalTheory.MomOne.ShiftComp.main | (intros; apply GlobalTheory.MomOne.ShiftComp.main <;> assumption)
