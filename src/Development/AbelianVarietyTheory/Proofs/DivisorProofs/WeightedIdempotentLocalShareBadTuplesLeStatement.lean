module

public import Formalism.SharpRestriction.LevelLetterCocycles.ArithmeticCylinders
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeightedIdempotentLocalShareBadTuplesLe
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.ArithmeticCylinders

theorem _root_.GlobalTheory.T.weightedIdempotent_localShare_bad_tuples_le : ∀ (D : D7) (ψ₀ : ∀ k : Fin 2, AddChar (ZMod (D.host.g k)) ℂ), (∀ k, ψ₀ k ≠ 1) → admLq D → TieAdmG D → 100 ≤ D.R.r → (∀ k : Fin 2, 2 ^ 12 ≤ D.host.g k) → ∀ (k : Fin 2) (S : Finset (Tup D k)), (∀ t ∈ S, ¬ goodAt D k t) → locShare D (fun k _ => eUk D k (ψ₀ k)) k S ≤ 3 * (D.R.f : ℝ) / (D.host.g k : ℝ) + 23 * (D.R.f : ℝ) * Real.log (D.host.g k : ℝ) / Real.sqrt (D.host.g k : ℝ) + 2 * (D.R.f : ℝ) * (D.R.m : ℝ) * (1 / (4 * ((min D.host.q D.host.d : ℕ) : ℝ)) + (1 + Real.log (D.R.r : ℝ)) / ((D.host.g k : ℝ) - 1)) + (D.R.r : ℝ) / 2 * (7 / 8 : ℝ) ^ D.R.f + Real.exp (-(D.R.f : ℝ) / (5 * Real.log (D.R.r : ℝ))) := by
  first | exact @GlobalTheory.PropWU.propW_eUk | exact GlobalTheory.PropWU.propW_eUk | (intros; apply GlobalTheory.PropWU.propW_eUk <;> assumption)
