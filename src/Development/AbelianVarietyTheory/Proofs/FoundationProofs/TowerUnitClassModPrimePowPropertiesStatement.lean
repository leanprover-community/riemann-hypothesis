module

public import Development.AbelianVarietyTheory.Definitions.Foundations.Letter
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.TowerUnitClassModPrimePowProperties
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
import Development.AbelianVarietyTheory.Definitions.Foundations.IsRootOne

@[expose] public section

open GlobalTheory.KZ GlobalTheory.KZ.H3 Matrix
open scoped MatrixGroups TensorProduct

theorem _root_.GlobalTheory.T.towerUnitClassModPrimePow_properties : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε) (l : ℕ) [Fact l.Prime], ∀ n : ℕ, (∀ y, ∃ f, X.cls l n f = y) ∧ (∀ f f' : X.Kˣ, X.cls l n f = X.cls l n f' ↔ ∃ g : X.Kˣ, f = f' * g ^ (l ^ n)) ∧ (∀ f f' : X.Kˣ, X.cls l n (f * f') = X.cls l n f + X.cls l n f') ∧ X.cls l n 1 = 0 ∧ (∀ (c : ℤ_[l]) (f : X.Kˣ), c • X.cls l n f = X.cls l n (f ^ (PadicInt.toZModPow n c).val)) ∧ (∀ (φ : X.K ≃+* X.K) (x : X.Khat l) (f : X.Kˣ), AdicCompletion.eval (idl l) (X.Kl l) n x = X.cls l n f → AdicCompletion.eval (idl l) (X.Kl l) n (X.kmap l φ x) = X.cls l n (Units.map φ.toMonoidHom f)) ∧ (∀ (x : X.Khat l) (f : X.Kˣ), AdicCompletion.eval (idl l) (X.Kl l) (n + 1) x = X.cls l (n + 1) f → AdicCompletion.eval (idl l) (X.Kl l) n x = X.cls l n f) := by
  first | exact @GlobalTheory.KZ.H3.cls_props | exact GlobalTheory.KZ.H3.cls_props | (intros; apply GlobalTheory.KZ.H3.cls_props <;> assumption)
