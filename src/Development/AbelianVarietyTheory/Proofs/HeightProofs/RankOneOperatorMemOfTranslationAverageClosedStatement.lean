module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NormDwLeSobNorm
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.RankOneOperatorMemOfTranslationAverageClosed
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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

open MeasureTheory Matrix Filter Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.SmoothGlob GlobalTheory.TypeSum
open scoped InnerProductSpace Topology

theorem _root_.GlobalTheory.T.rankOneOperator_mem_of_translation_average_closed : ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : Mx n → (H →L[ℂ] H)), Std ε σ → ∀ Q : (H → H) → Prop, (∀ g ∈ UJset ε, Q (σ g)) → (∀ T T' : H → H, Q T → Q T' → Q (fun w => T w + T' w) ∧ Q (fun w => T (T' w))) → (∀ (c : ℂ) (T : H → H), Q T → Q (fun w => c • T w)) → (∀ e : KG ε → ℂ, KFinFun ε e → Q (kAvg ε σ e)) → Q (fun _ => 0) → ∀ e : KG ε → ℂ, KFinFun ε e → ∃ (m : ℕ) (a c : Fin m → H), (∀ j, IsKFin ε σ (a j)) ∧ (∀ w, kAvg ε σ e w = ∑ j, ⟪c j, w⟫_ℂ • a j) ∧ ∀ j u, IsKFin ε σ u → Q (fun w => ⟪c j, w⟫_ℂ • u) := by
  first | exact @GlobalTheory.TypeSum.rank_one_mem_of_closed | exact GlobalTheory.TypeSum.rank_one_mem_of_closed | (intros; apply GlobalTheory.TypeSum.rank_one_mem_of_closed <;> assumption)
