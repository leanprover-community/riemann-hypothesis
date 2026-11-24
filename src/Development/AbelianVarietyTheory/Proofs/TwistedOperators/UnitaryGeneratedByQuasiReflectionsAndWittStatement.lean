module

public import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.IsHermHyperbolic
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnitaryGeneratedByQuasiReflectionsAndWitt
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

open scoped Matrix

theorem _root_.GlobalTheory.T.unitary_generated_by_quasiReflections_and_witt : ∀ (E : Type) [Field E] [CharZero E] (n : ℕ) (σ : E →+* E) (G : Matrix (Fin n) (Fin n) E), GlobalTheory.UTrans.IsHerm σ G → (∀ γ, GlobalTheory.UTrans.IsU σ G γ → ∃ l : List ((Fin n → E) × E), (∀ p ∈ l, GlobalTheory.UTrans.hf σ G p.1 p.1 ≠ 0 ∧ p.2 * σ p.2 = 1) ∧ γ = (l.map fun p => GlobalTheory.UTrans.tv σ G p.1 ((p.2 - 1) / GlobalTheory.UTrans.hf σ G p.1 p.1)).prod) ∧ ∀ x z : Fin n → E, GlobalTheory.UTrans.hf σ G x x ≠ 0 → GlobalTheory.UTrans.hf σ G z z = GlobalTheory.UTrans.hf σ G x x → ∃ γ, GlobalTheory.UTrans.IsU σ G γ ∧ γ *ᵥ z = x := by
  first | exact @GlobalTheory.UTrans.ReflChar0.gen_and_witt | exact GlobalTheory.UTrans.ReflChar0.gen_and_witt | (intros; apply GlobalTheory.UTrans.ReflChar0.gen_and_witt <;> assumption)
