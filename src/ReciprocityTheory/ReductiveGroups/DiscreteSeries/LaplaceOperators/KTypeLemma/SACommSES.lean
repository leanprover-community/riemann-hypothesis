module

public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.KTypeLemma.TensorActionApplyDual
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.KTypeLemma.PartialSumRootEq
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.KTypeLemma.LowestWeightLiftLemmas

@[expose] public section

noncomputable section

open Finset

namespace ReciprocityTheory.ChartRestriction.DS.Lap.LemK

open ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ} {M : Type*} [AddCommGroup M] [Module ℂ M] {MM : Type*} [AddCommGroup MM] [Module ℂ MM]

theorem sA_isKRel (ε : Fin n → Bool) (E : Fin n → Fin n → Module.End ℂ M) (V : Submodule ℂ M)
    (hV : IsKStableSub ε E V) (hE : IsGlRep E) : IsKRel ε (sA ε E V hV) := by
  intros; apply ReciprocityTheory.ChartRestriction.DS.Lap.LemK.KernelRelationLemmas.sA_isKRel <;> assumption

theorem sA_comm_sES (ε : Fin n → Bool) (E : Fin n → Fin n → Module.End ℂ M) (V : Submodule ℂ M)
    (hV : IsKStableSub ε E V) (a b : Fin n) (hab : ε a = ε b) : Commute (sA ε E V hV a b) (sES V) := by
  intros; apply ReciprocityTheory.ChartRestriction.DS.Lap.LemK.KernelRelationLemmas.sA_comm_sES <;> assumption

theorem sθ_sA (ε : Fin n → Bool) (E : Fin n → Fin n → Module.End ℂ M) (V : Submodule ℂ M)
    (hV : IsKStableSub ε E V) (EM : Fin n → Fin n → Module.End ℂ MM) (hEM : IsGlRep EM) (φ : MM)
    (ν Λ : Fin n → ℝ) (hφ : ∀ a, EM a a φ = ((ν a : ℝ) : ℂ) • φ) (ℓ : V →ₗ[ℂ] ℂ)
    (hℓ : ∀ (a : Fin n) (v w : V), (w : M) = E a a v → ℓ w = ((Λ a : ℝ) : ℂ) * ℓ v) (a : Fin n)
    (x : KS (n := n) V) :
    sθ V EM φ ℓ (sA ε E V hV a a x) =
      tensV EM a a (sθ V EM φ ℓ x) + ((Λ a - ν a : ℝ) : ℂ) • sθ V EM φ ℓ x := by
  intros; apply ReciprocityTheory.ChartRestriction.DS.Lap.LemK.KernelRelationLemmas.sθ_sA <;> assumption

theorem sT_sA (ε : Fin n → Bool) (E : Fin n → Fin n → Module.End ℂ M) (V : Submodule ℂ M)
    (hV : IsKStableSub ε E V) (hE : IsGlRep E) (a b : Fin n) (hab : ε a = ε b) (x : KS (n := n) V) :
    sT E V (sA ε E V hV a b x) = tensV E a b (sT E V x) := by
  intros; apply ReciprocityTheory.ChartRestriction.DS.Lap.LemK.KernelRelationLemmas.sT_sA <;> assumption

end ReciprocityTheory.ChartRestriction.DS.Lap.LemK
