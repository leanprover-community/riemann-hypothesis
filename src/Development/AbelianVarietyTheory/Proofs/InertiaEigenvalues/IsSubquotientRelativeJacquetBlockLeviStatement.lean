module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsSubquotientOfEquiv
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsSubquotientRelativeJacquetBlockLevi
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

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.JacStages

theorem _root_.GlobalTheory.T.isSubquotient_relativeJacquet_blockLevi : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (s : ℕ) (d : Fin s → ℕ) (t : Fin s → ℕ) (d' : ∀ a, Fin (t a) → ℕ)
    (e' : ∀ a, (Σ b, Fin (d' a b)) ≃ Fin (d a)) (V W : Type) [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W] (σ : Representation ℂ (Levi k fun a => Fin (d a)) V)
    (τ : Representation ℂ (Levi k fun a => Fin (d a)) W),
    IsSmooth τ → IsSubquotient σ τ → IsSubquotient (relJacD e' σ) (relJacD e' τ) := by
  first | exact @GlobalTheory.JacStagesExact.isSubquotient_relJacD | exact GlobalTheory.JacStagesExact.isSubquotient_relJacD | (intros; apply GlobalTheory.JacStagesExact.isSubquotient_relJacD <;> assumption)
