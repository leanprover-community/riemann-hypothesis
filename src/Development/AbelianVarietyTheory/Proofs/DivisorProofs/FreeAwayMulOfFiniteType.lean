module

public import Mathlib.RingTheory.Algebraic.Defs
public import Mathlib.RingTheory.FiniteType
public import Mathlib.RingTheory.Localization.Away.Basic
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsPowSmulMemRangeOfSurjectiveBaseChange
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
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open TensorProduct

namespace GlobalTheory

theorem free_away_mul_of_finiteType : ∀ {A B : Type} [CommRing A] [CommRing B] [IsDomain A] [IsNoetherianRing A] [Algebra A B] [Algebra.FiniteType A B] [Algebra.IsAlgebraic A B], ∃ a : A, a ≠ 0 ∧ ∀ (c : A) (A' B' : Type) [CommRing A'] [CommRing B'] [Algebra A A'] [Algebra B B'] [Algebra A' B'] [Algebra A B'] [IsScalarTower A A' B'] [IsScalarTower A B B'], IsLocalization.Away (a * c) A' → IsLocalization.Away (algebraMap A B (a * c)) B' → Module.Free A' B' := by
  intro A B _ _ _ _ _ _ _
  obtain ⟨a, ha0, hfree⟩ := (generic_freeness A).2.1 B B
  refine ⟨a, ha0, fun c A' B' _ _ _ _ _ _ _ _ hA hB => ?_⟩
  haveI := hA
  have hu : IsUnit (algebraMap A A' a) := by
    have := IsLocalization.Away.algebraMap_isUnit (S := A') (a * c)
    rw [map_mul] at this
    exact isUnit_of_mul_isUnit_left this
  letI : Algebra (Localization.Away a) A' :=
    (IsLocalization.Away.lift a (S := Localization.Away a) hu).toAlgebra
  haveI : IsScalarTower A (Localization.Away a) A' :=
    IsScalarTower.of_algebraMap_eq fun x =>
      (IsLocalization.Away.lift_eq (S := Localization.Away a) a hu x).symm
  haveI : Module.Free (Localization.Away a) ((Localization.Away a) ⊗[A] B) :=
    Module.Free.of_equiv (LocalizedModule.equivTensorProduct (Submonoid.powers a) B)
  haveI : Module.Free A' (A' ⊗[A] B) :=
    Module.Free.of_equiv (TensorProduct.AlgebraTensorModule.cancelBaseChange A
      (Localization.Away a) A' A' B)
  haveI hloc : IsLocalizedModule (Submonoid.powers (a * c))
      (IsScalarTower.toAlgHom A B B').toLinearMap := by
    rw [isLocalizedModule_iff_isLocalization, Algebra.algebraMapSubmonoid, Submonoid.map_powers]
    exact hB
  have hbc := IsLocalizedModule.isBaseChange (Submonoid.powers (a * c)) A'
    (IsScalarTower.toAlgHom A B B').toLinearMap
  exact Module.Free.of_equiv hbc.equiv

end GlobalTheory
