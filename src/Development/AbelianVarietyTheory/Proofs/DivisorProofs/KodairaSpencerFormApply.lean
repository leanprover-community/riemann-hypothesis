module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.QActMSubAlgebraMap
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.InfUniv
import Development.AbelianVarietyTheory.Definitions.Divisors.KottwitzDimSignatureOneOne

@[expose] public section

open Module GlobalTheory.HTRho GlobalTheory.UPel.Sm GlobalTheory.UPel.Sm.Model

namespace GlobalTheory.HTRho

theorem finrank_homO_eq_quot_mSub : ∀ {k O C W V : Type*} [Field k] [Ring O] [CommRing C] [Algebra C O]
    [AddCommGroup W] [Module k W] [FiniteDimensional k W] [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    (σW : O →+* Module.End k W) (τ : O →+* Module.End k V) (χ : C →+* k),
    (∀ c, τ (algebraMap C O c) = χ c • 1) →
    finrank k (homO σW τ) = finrank k (homO (qAct σW (mSub σW χ ⊤) (mSub_stable σW χ ⊤ (fun _ _ _ => trivial))) τ) := by
  intro k O C W V _ _ _ _ _ _ _ _ _ _ σW τ χ hτ
  have hker : ∀ T : W →ₗ[k] V, T ∈ homO σW τ → mSub σW χ ⊤ ≤ LinearMap.ker T := by
    intro T hT
    rw [mem_homO] at hT
    refine Submodule.span_le.mpr ?_
    rintro z ⟨c, x, -, rfl⟩
    simp only [SetLike.mem_coe, LinearMap.mem_ker, map_sub, map_smul, hT, hτ, LinearMap.smul_apply,
      Module.End.one_apply, sub_self]
  let qa := qAct σW (mSub σW χ ⊤) (mSub_stable σW χ ⊤ (fun _ _ _ => trivial))
  let e : homO qa τ ≃ₗ[k] homO σW τ :=
    { toFun := fun f => ⟨f.1 ∘ₗ (mSub σW χ ⊤).mkQ, by
        rw [mem_homO]
        intro a x
        have h := (mem_homO _ _ _).mp f.2 a ((mSub σW χ ⊤).mkQ x)
        change f.1 ((mSub σW χ ⊤).mkQ (σW a x)) = τ a (f.1 ((mSub σW χ ⊤).mkQ x))
        rw [← qAct_mk]
        exact h⟩
      invFun := fun T => ⟨(mSub σW χ ⊤).liftQ T.1 (hker T.1 T.2), by
        rw [mem_homO]
        intro a y
        induction y using Submodule.Quotient.induction_on with
        | H x =>
          have h := (mem_homO _ _ _).mp T.2 a x
          change (mSub σW χ ⊤).liftQ T.1 _ (qa a ((mSub σW χ ⊤).mkQ x)) = τ a ((mSub σW χ ⊤).liftQ T.1 _ ((mSub σW χ ⊤).mkQ x))
          simp only [qa, qAct_mk, Submodule.liftQ_mkQ, Submodule.mkQ_apply, Submodule.liftQ_apply]
          exact h⟩
      map_add' := fun f g => by ext; rfl
      map_smul' := fun c f => by ext; rfl
      left_inv := fun f => by
        ext y
        rfl
      right_inv := fun T => by ext; rfl }
  exact e.finrank_eq.symm

end GlobalTheory.HTRho
