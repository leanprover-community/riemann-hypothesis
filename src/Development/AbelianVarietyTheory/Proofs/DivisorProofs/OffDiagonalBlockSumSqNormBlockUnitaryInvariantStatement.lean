module

public import Formalism.RealPlaceAnalysis.Complexify
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OffDiagonalBlockSumSqNormBlockUnitaryInvariant
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

open MeasureTheory Matrix
open Formalism.REAL (UJ KG toM toMK muK expG inG Jm Kset)

theorem _root_.GlobalTheory.T.offDiagonalBlock_sum_sq_norm_blockUnitary_invariant : ∀ (n : ℕ) (ε : Fin n → Bool) (a b g : Matrix (Fin n) (Fin n) ℂ), aᴴ * a = 1 → a * Jm ε = Jm ε * a → bᴴ * b = 1 → b * Jm ε = Jm ε * b → ∑ z : {z : Fin n × Fin n // ε z.1 = true ∧ ε z.2 = false}, ‖(a * g * b) z.1.1 z.1.2‖ ^ 2 = ∑ z : {z : Fin n × Fin n // ε z.1 = true ∧ ε z.2 = false}, ‖(g) z.1.1 z.1.2‖ ^ 2 := by
  first | exact @GlobalTheory.offDiag_sum_sq_norm_unitary_invariant | exact GlobalTheory.offDiag_sum_sq_norm_unitary_invariant | (intros; apply GlobalTheory.offDiag_sum_sq_norm_unitary_invariant <;> assumption)
