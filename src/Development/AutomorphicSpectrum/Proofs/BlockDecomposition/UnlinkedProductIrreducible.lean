module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TwoSegmentNongenericQuotient
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL

namespace GlobalTheory.CompanionTheory.BZSeg.Unlinked

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {N : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]

def subIncl (π : Representation ℂ (GL (Fin N) k) V) (S : Subrepresentation π) :
    S.toRepresentation.IntertwiningMap π where
  toLinearMap := S.toSubmodule.subtype
  isIntertwining' := fun _ => rfl

def quotProj {W : Type} [AddCommGroup W] [Module ℂ W] (π : Representation ℂ (GL (Fin N) k) V)
    (σ : Representation ℂ (GL (Fin N) k) W) (f : σ.IntertwiningMap π) :
    π.IntertwiningMap (GlobalTheory.CompanionTheory.BZSeg.TwoSeg.quotRep π σ f) where
  toLinearMap := (LinearMap.range f.toLinearMap).mkQ
  isIntertwining' := fun _ => rfl

theorem isIrreducible_of_generic {ψ : AddChar k Circle} (hψ : Continuous ψ) (h1 : ψ ≠ 1)
    (π : Representation ℂ (GL (Fin N) k) V) [Nontrivial V] (hπ : IsSmooth π)
    (hr : Module.rank ℂ (TwJacquet π (unipB k (Fin N)) (whitChar ψ N)) ≤ 1)
    (hsub : ∀ (W : Type) [AddCommGroup W] [Module ℂ W] (σ : Representation ℂ (GL (Fin N) k) W)
      (f : σ.IntertwiningMap π), Function.Injective f → Nontrivial W → IsGeneric σ)
    (hquo : ∀ (W : Type) [AddCommGroup W] [Module ℂ W] (τ : Representation ℂ (GL (Fin N) k) W)
      (f : π.IntertwiningMap τ), Function.Surjective f → Nontrivial W → IsGeneric τ) :
    π.IsIrreducible := by
  have hbt : (⊥ : Subrepresentation π) ≠ ⊤ := by
    intro e
    obtain ⟨v, hv⟩ := exists_ne (0 : V)
    have h2 : v ∈ (⊤ : Subrepresentation π).toSubmodule := trivial
    rw [← e] at h2
    exact hv h2
  haveI : Nontrivial (Subrepresentation π) := ⟨⟨⊥, ⊤, hbt⟩⟩
  refine ⟨fun S => ?_⟩
  by_contra hc
  push Not at hc
  obtain ⟨hb, ht⟩ := hc
  have hinj : Function.Injective (subIncl π S) := Subtype.val_injective
  have hSn : Nontrivial S.toSubmodule := by
    by_contra hn
    rw [not_nontrivial_iff_subsingleton] at hn
    refine hb (Subrepresentation.toSubmodule_injective ?_)
    refine (Submodule.eq_bot_iff _).2 fun v hv => ?_
    exact congrArg Subtype.val (Subsingleton.elim (⟨v, hv⟩ : S.toSubmodule) 0)
  have hrange : LinearMap.range (subIncl π S).toLinearMap = S.toSubmodule := Submodule.range_subtype _
  have hQn : Nontrivial (V ⧸ LinearMap.range (subIncl π S).toLinearMap) := by
    refine Submodule.Quotient.nontrivial_iff.2 ?_
    rw [hrange]
    intro e
    exact ht (Subrepresentation.toSubmodule_injective e)
  have hσ := hsub _ S.toRepresentation (subIncl π S) hinj hSn
  exact GlobalTheory.CompanionTheory.BZSeg.TwoSeg.not_isGeneric_quotRep hψ h1 π _ (subIncl π S) hinj hπ hr hσ
    (hquo _ _ (quotProj π _ (subIncl π S)) (Submodule.mkQ_surjective _) hQn)

end GlobalTheory.CompanionTheory.BZSeg.Unlinked

end
