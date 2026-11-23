module

public import Mathlib.RingTheory.Smooth.Basic
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsSmoothFreeAway
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Linter.Style
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

open scoped TensorProduct

namespace GlobalTheory

theorem exists_smooth_subalgebra_of_finset : ∀ (F K : Type) [Field F] [CharZero F] [Field K]
    [Algebra F K] (s : Finset K), ∃ R : Subalgebra F K, (↑s : Set K) ⊆ (R : Set K) ∧
      Algebra.Smooth F R := by
  intro F K _ _ _ _ s
  haveI : PerfectField F := PerfectField.ofCharZero
  let C : Subalgebra F K := Algebra.adjoin F (↑s : Set K)
  haveI : Algebra.FiniteType F C :=
    ⟨(Subalgebra.fg_top C).mpr (Subalgebra.fg_adjoin_finset s)⟩
  obtain ⟨f, hf0, hsm, -⟩ := GlobalTheory.SS.exists_smooth_free_away F C C
  have hinjC : Function.Injective (algebraMap C K) := Subtype.val_injective
  have hfK : IsUnit (algebraMap C K f) := by
    refine isUnit_iff_ne_zero.mpr ?_
    intro h
    exact hf0 (hinjC (by simpa using h))
  let g : Localization.Away f →ₐ[F] K :=
    { IsLocalization.Away.lift f hfK with
      commutes' := fun r => by
        show IsLocalization.Away.lift f hfK (algebraMap F (Localization.Away f) r) = algebraMap F K r
        rw [IsScalarTower.algebraMap_apply F C (Localization.Away f),
          IsLocalization.Away.lift_eq]
        rfl }
  have hginj : Function.Injective g := by
    show Function.Injective (IsLocalization.Away.lift f hfK)
    rw [IsLocalization.Away.lift, IsLocalization.lift_injective_iff]
    intro x y
    constructor
    · intro h
      rw [IsLocalization.injective (Localization.Away f) (powers_le_nonZeroDivisors_of_noZeroDivisors hf0) h]
    · intro h
      have : x = y := hinjC h
      rw [this]
  refine ⟨g.range, ?_, ?_⟩
  · intro x hx
    refine ⟨algebraMap C (Localization.Away f) ⟨x, Algebra.subset_adjoin hx⟩, ?_⟩
    show IsLocalization.Away.lift f hfK _ = x
    rw [IsLocalization.Away.lift_eq]
    rfl
  · exact Algebra.Smooth.of_equiv (AlgEquiv.ofInjective g hginj)
end GlobalTheory
