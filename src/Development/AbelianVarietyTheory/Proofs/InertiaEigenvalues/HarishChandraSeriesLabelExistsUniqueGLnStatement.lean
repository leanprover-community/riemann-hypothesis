module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LabelDatum
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HarishChandraSeriesLabelExistsUniqueGLn
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

open GlobalTheory.GLq Formalism.MainNotions.ArithmeticCylinders Polynomial
open scoped Classical

theorem _root_.GlobalTheory.T.harishChandraSeriesLabel_exists_unique_GLn : ∀ (g : ℕ) [Fact g.Prime] (L : LabelDatum g), 5 ≤ g → Green → ∀ (n : ℕ), (∀ χ : Gn g n → ℂ, IsIrr χ → ∃! f, HasLabel L χ f) ∧ (∀ (χ : Gn g n → ℂ) f, HasLabel L χ f → f.Monic ∧ f.natDegree = n ∧ f.coeff 0 ≠ 0) ∧ ∀ f : (ZMod g)[X], f.Monic → f.natDegree = n → f.coeff 0 ≠ 0 → Squarefree f → ∃ Q : List ((ZMod g)[X] × Pc g), (∀ p ∈ Q, IsCuspOf L p.1 p.2.2 ∧ p.2.2 1 = ∏ i ∈ Finset.Ico 1 p.2.1, ((g : ℂ) ^ i - 1)) ∧ ((Q.map Prod.fst : List _) : Multiset _) = UniqueFactorizationMonoid.normalizedFactors f ∧ degL (Q.map Prod.snd) = n ∧ {χ : Gn g n → ℂ | IsIrr χ ∧ HasLabel L χ f} = {hcL (Q.map Prod.snd) n} := by
  first | exact @GlobalTheory.GLq.Label.label_main | exact GlobalTheory.GLq.Label.label_main | (intros; apply GlobalTheory.GLq.Label.label_main <;> assumption)
