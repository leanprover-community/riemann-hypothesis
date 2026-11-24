module

public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.IsComplementaryProductOfIsCuspidal
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL ValuativeRel MeasureTheory

namespace GlobalTheory.UnitaryDual

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def IsSquareIntegrable (δ : IrrGL (k := k)) : Prop :=
  0 < δ.1 ∧ IsUnitarisable δ.rep ∧
    letI : MeasurableSpace (GL (Fin δ.1) k ⧸ Subgroup.center (GL (Fin δ.1) k)) := borel _
    ∃ μ : Measure (GL (Fin δ.1) k ⧸ Subgroup.center (GL (Fin δ.1) k)), μ.IsHaarMeasure ∧
      ∀ v, ∀ ℓ ∈ smoothPart δ.rep.dual, ∫⁻ q, ‖ℓ (δ.rep q.out v)‖ₑ ^ 2 ∂μ < ⊤

def IsUnitarySpeh (x : IrrGL (k := k)) : Prop := ∃ (δ : IrrGL (k := k)) (m : ℕ), IsSquareIntegrable δ ∧ 1 ≤ m ∧ IsSpeh δ m x.rep

end GlobalTheory.UnitaryDual

namespace GlobalTheory.Published

open GlobalTheory.UnitaryDual

def UnitaryDualGL : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [CharZero k]
    (N : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V),
    IsSmooth π → π.IsIrreducible → IsUnitarisable π →
    ∃ (u : List (IrrGL (k := k))) (τ : List (IrrGL (k := k) × ℝ)), (∀ x ∈ u, IsUnitarySpeh x) ∧
      (∀ p ∈ τ, IsUnitarySpeh p.1 ∧ 0 < p.2 ∧ p.2 < 1 / 2) ∧
      ∃ (h : ℕ) (x : Fin h → IrrGL (k := k)) (hd : ∑ a, (x a).1 = N), List.ofFn x = GenericUnitary.factors u τ ∧
        Nonempty (π.Equiv (prodIrr x hd))

end GlobalTheory.Published

end
