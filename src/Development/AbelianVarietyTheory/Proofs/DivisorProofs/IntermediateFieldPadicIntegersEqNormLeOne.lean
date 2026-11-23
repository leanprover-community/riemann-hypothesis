module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClassesAt
public import Formalism.LocalRingCardinality.SpanPowerMembership.NDLocE
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Tactic.NormNum.Prime
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LamGApply

@[expose] public section

open NumberField IsDedekindDomain
open scoped TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.L2.Pj GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.ExpFrame GlobalTheory.ExpTie GlobalTheory.FrameOf
open Formalism.CohomologicalDescent.DepthNonnegative Formalism.CohomologicalDescent.LD Formalism.GradedWeylDivisibility MvPolynomial
open GlobalTheory.FrameRead
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FrameOf

theorem intEmb_range_norm_le_one : ∀ (l : ℕ) [Fact l.Prime] (Lf : IntermediateField ℚ_[l] (PadicAlgCl l)) [FiniteDimensional ℚ_[l] Lf],
    Function.Injective (intEmb Lf) ∧ ∀ x, x ∈ Set.range (intEmb Lf) ↔ x ∈ Lf ∧ ‖x‖ ≤ 1 := by
  intro l _ Lf _
  refine ⟨fun a b h => Subtype.ext (Subtype.ext h), fun x => ?_⟩
  constructor
  · rintro ⟨a, rfl⟩
    refine ⟨(a : Lf).2, ?_⟩
    rw [← Formalism.BasicNotions.Examples₂.LB.isIntegral_iff_norm_le]
    have ha : IsIntegral ℤ_[l] (a : Lf) := a.2
    exact ha.map (Lf.val.restrictScalars ℤ_[l])
  · rintro ⟨hx, hn⟩
    rw [← Formalism.BasicNotions.Examples₂.LB.isIntegral_iff_norm_le] at hn
    have hi : IsIntegral ℤ_[l] (⟨x, hx⟩ : Lf) :=
      (isIntegral_algHom_iff (Lf.val.restrictScalars ℤ_[l]) Subtype.val_injective).1 hn
    exact ⟨⟨⟨x, hx⟩, hi⟩, rfl⟩

end GlobalTheory.FrameOf

end
