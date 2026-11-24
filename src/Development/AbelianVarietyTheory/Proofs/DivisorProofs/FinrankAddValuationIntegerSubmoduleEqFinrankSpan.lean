module

public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.MultiplicationKernelIdentity
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsSaturatedSubmoduleIffExistsIsComplOfValuationR
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
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.TotallySplit
import Mathlib.RingTheory.Valuation.Extension
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PreEig

@[expose] public section

open GlobalTheory.IndefiniteRowSideFullHecke.MultiplicationKernelIdentity GlobalTheory.HermitianPreEigenvalues Polynomial Module

namespace GlobalTheory

theorem finrank_addValuationInteger_submodule_eq_finrank_span : ∀ (C : Type) [Field C] (v : AddValuation C (WithTop ℝ))
    (N : ℕ) (X : Submodule (Int0 v) (Fin N → Int0 v)), Module.Finite (Int0 v) X →
    finrank (Int0 v) X = finrank C (Submodule.span C ((fun (x : Fin N → Int0 v) (i : Fin N) =>
      (x i : C)) '' (X : Set (Fin N → Int0 v)))) := by
  intro C _ v N X hX
  let ι : (Fin N → Int0 v) →ₗ[Int0 v] (Fin N → C) := (Algebra.linearMap (Int0 v) C).compLeft (Fin N)
  have hι : Function.Injective ι := by
    intro x y h; funext i; exact Subtype.ext (congrFun h i)
  let L : X →ₗ[Int0 v] (Fin N → C) := ι ∘ₗ X.subtype
  have hL : Function.Injective L := hι.comp Subtype.val_injective
  have hInt : v.toValuation.Integers (Int0 v) := by
    refine ⟨Subtype.val_injective, ?_, ?_⟩
    · intro x
      change 0 ≤ v (x : C)
      exact (mem_addValuationIntegerRing_iff v _).mp x.property
    · intro x hx
      change 0 ≤ v x at hx
      exact ⟨⟨x, (mem_addValuationIntegerRing_iff v x).mpr hx⟩, rfl⟩
  have : ValuationRing (Int0 v) := ValuationRing.of_integers _ hInt
  have : IsFractionRing (Int0 v) C := hInt.isFractionRing
  have : Module.IsTorsionFree (Int0 v) X := inferInstance
  have : Module.Free (Int0 v) X := free_of_finite_of_isTorsionFree_of_valuationRing (Int0 v) X
  let b := Module.Free.chooseBasis (Int0 v) X
  have hli : LinearIndependent (Int0 v) (L ∘ b) :=
    b.linearIndependent.map' L (LinearMap.ker_eq_bot.mpr hL)
  have hliC : LinearIndependent C (L ∘ b) := (LinearIndependent.iff_fractionRing (Int0 v) C).mp hli
  have hspan : Submodule.span C ((fun (x : Fin N → Int0 v) (i : Fin N) => (x i : C)) ''
      (X : Set (Fin N → Int0 v))) = Submodule.span C (Set.range (L ∘ b)) := by
    apply le_antisymm
    · rw [Submodule.span_le]
      rintro _ ⟨x, hx, rfl⟩
      have h1 : L ⟨x, hx⟩ ∈ Submodule.span (Int0 v) (L '' Set.range b) :=
        Submodule.apply_mem_span_image_of_mem_span L (by rw [b.span_eq]; trivial)
      rw [← Set.range_comp] at h1
      exact Submodule.span_le_restrictScalars (Int0 v) C _ h1
    · rw [Submodule.span_le]
      rintro _ ⟨k, rfl⟩
      exact Submodule.subset_span ⟨(b k : Fin N → Int0 v), (b k).2, rfl⟩
  rw [hspan, finrank_span_eq_card hliC, Module.finrank_eq_card_chooseBasisIndex]

end GlobalTheory
