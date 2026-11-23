module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.BaseLengthBound.MonoCount
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.Tactic.Linter.Style
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

open Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.BasicNotions NumberField IsDedekindDomain Module Formalism.MainNotions.Gaps.EtaleWeightGaps

namespace PoleLengthBounds

theorem lenPiU_holds : LenPiU := by
  intro R E V _ _ _ _ _ ι _ A B U hU
  classical
  set A' : Submodule R (ι → E) := Submodule.pi Set.univ fun _ => A with hA'
  set B' : Submodule R (ι → E) := Submodule.pi Set.univ fun _ => B with hB'
  let e : ↥A' ≃ₗ[R] ↥(A'.map U) := Submodule.equivMapOfInjective U hU A'
  have he : ∀ x : ↥A', ((e x : ↥(A'.map U)) : V) = U x := fun _ => rfl
  have hmap : (B'.comap A'.subtype).map (e : ↥A' →ₗ[R] ↥(A'.map U)) = (B'.map U).comap (A'.map U).subtype := by
    ext y
    rw [Submodule.mem_map_equiv, Submodule.mem_comap, Submodule.mem_comap, Submodule.subtype_apply,
      Submodule.subtype_apply]
    obtain ⟨x, rfl⟩ := e.surjective y
    rw [LinearEquiv.symm_apply_apply, he]
    exact ⟨fun h => ⟨x, h, rfl⟩, fun ⟨z, hz, h⟩ => hU h ▸ hz⟩
  rw [← (Submodule.Quotient.equiv _ _ e hmap).length_eq]

  let f : ↥A' →ₗ[R] (ι → ↥A ⧸ B.comap A.subtype) :=
    LinearMap.pi fun i => (B.comap A.subtype).mkQ ∘ₗ
      LinearMap.codRestrict A ((LinearMap.proj i : (ι → E) →ₗ[R] E) ∘ₗ A'.subtype)
        (fun x => x.2 i (Set.mem_univ i))
  have hf : Function.Surjective f := by
    intro g
    choose a ha using fun i => Submodule.Quotient.mk_surjective _ (g i)
    refine ⟨⟨fun i => a i, fun i _ => (a i).2⟩, ?_⟩
    funext i
    exact ha i
  have hker : LinearMap.ker f = B'.comap A'.subtype := by
    ext x
    simp only [LinearMap.mem_ker, Submodule.mem_comap, Submodule.subtype_apply]
    constructor
    · intro h i _
      have h' : (B.comap A.subtype).mkQ
          (LinearMap.codRestrict A ((LinearMap.proj i : (ι → E) →ₗ[R] E) ∘ₗ A'.subtype)
            (fun x => x.2 i (Set.mem_univ i)) x) = 0 := congrFun h i
      rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at h'
      exact h'
    · intro h
      funext i
      show (B.comap A.subtype).mkQ
          (LinearMap.codRestrict A ((LinearMap.proj i : (ι → E) →ₗ[R] E) ∘ₗ A'.subtype)
            (fun x => x.2 i (Set.mem_univ i)) x) = 0
      rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
      exact h i (Set.mem_univ i)
  rw [← hker, (f.quotKerEquivOfSurjective hf).length_eq, Module.length_pi, ENat.card_eq_coe_fintype_card]

end PoleLengthBounds
