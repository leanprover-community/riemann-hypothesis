module

public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.MinorOrderedEntries
public import Mathlib.RepresentationTheory.Intertwining
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NonemptyInvFunEquiv
import Mathlib.Algebra.Module.StablyFree.Basic
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open MvPolynomial GlobalTheory.IndefiniteRowSideFullHecke.MinorOrderedEntries GlobalTheory.OneFunctional Formalism.BasicNotions GlobalTheory.Branching
open scoped TensorProduct DirectSum

namespace GlobalTheory.OneFunctional

theorem nonempty_invFun_dual_tprod_equiv (G V W : Type) [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup W]
    [Module ℂ W] [FiniteDimensional ℂ V] (ρ : Representation ℂ G V) (σ : Representation ℂ G W) :
    Nonempty (invFun (ρ.dual.tprod σ) ≃ₗ[ℂ] σ.IntertwiningMap ρ) := by
  let L : σ.IntertwiningMap ρ →ₗ[ℂ] invFun (ρ.dual.tprod σ) :=
    { toFun := fun f => ⟨TensorProduct.lift (LinearMap.lcomp ℂ ℂ f.toLinearMap), fun g x => by
        induction x with
        | tmul ξ w =>
          have h := LinearMap.congr_fun (f.isIntertwining' g) w
          simp only [LinearMap.comp_apply] at h
          simp only [Representation.tprod_apply, TensorProduct.map_tmul, TensorProduct.lift.tmul,
            LinearMap.lcomp_apply, Representation.dual_apply, Module.Dual.transpose_apply, LinearMap.comp_apply, h,
            Representation.inv_self_apply]
        | add a b ha hb => simp only [map_add (f := _), ha, hb]⟩
      map_add' := fun f f' => Subtype.ext (TensorProduct.ext' fun ξ w => by
        change ξ (f.toLinearMap w + f'.toLinearMap w) = ξ (f.toLinearMap w) + ξ (f'.toLinearMap w)
        exact map_add _ _ _)
      map_smul' := fun c f => Subtype.ext (TensorProduct.ext' fun ξ w => by
        change ξ (c • f.toLinearMap w) = c • ξ (f.toLinearMap w)
        exact map_smul _ _ _) }
  have hL : ∀ f ξ w, (L f).1 (ξ ⊗ₜ w) = ξ (f.toLinearMap w) := fun _ _ _ => rfl
  refine ⟨(LinearEquiv.ofBijective L ⟨fun f f' h => ?_, fun l => ?_⟩).symm⟩
  · refine Representation.IntertwiningMap.ext (LinearMap.ext fun w => ?_)
    refine (Module.evalEquiv ℂ V).injective (LinearMap.ext fun ξ => ?_)
    change ξ _ = ξ _
    rw [← hL, ← hL, h]
  · let φ : W →ₗ[ℂ] V := (Module.evalEquiv ℂ V).symm.toLinearMap ∘ₗ (TensorProduct.curry l.1).flip
    have hφ : ∀ (ξ : Module.Dual ℂ V) w, ξ (φ w) = l.1 (ξ ⊗ₜ w) := fun ξ w => by
      simp [φ]
    refine ⟨⟨φ, fun g => LinearMap.ext fun w => ?_⟩, Subtype.ext (TensorProduct.ext' fun ξ w => hφ ξ w)⟩
    refine (Module.evalEquiv ℂ V).injective (LinearMap.ext fun ξ => ?_)
    change ξ (φ (σ g w)) = (ξ ∘ₗ ρ g) (φ w)
    rw [hφ, hφ, ← mem_invFun.1 l.2 g ((ξ ∘ₗ ρ g) ⊗ₜ w), Representation.tprod_apply, TensorProduct.map_tmul]
    congr 2
    ext v
    simp [Module.Dual.transpose_apply]

end GlobalTheory.OneFunctional
