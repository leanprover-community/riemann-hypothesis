module

public import Formalism.HermitianCurvature.StatementU
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.UnitaryConjEntryAndInvEntryLinear
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants Finset

theorem _root_.GlobalTheory.T.unitary_conj_entry_and_inv_entry_linear : ∀ (k r : ℕ) (i j : Fin (2 * r + k + 1)), (∃ co : Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → ℂ, ∀ g ∈ B.GV k r, star (g i j) = ∑ a, ∑ b, co a b * g⁻¹ a b) ∧ ∃ q : B.Mat k r → ℂ, U.IsPolyDeg 1 q ∧ ∀ g ∈ B.GV k r, g⁻¹ i j = q g := by
  first | exact @GlobalTheory.unitary_conj_entry_and_inv_entry | exact GlobalTheory.unitary_conj_entry_and_inv_entry | (intros; apply GlobalTheory.unitary_conj_entry_and_inv_entry <;> assumption)
