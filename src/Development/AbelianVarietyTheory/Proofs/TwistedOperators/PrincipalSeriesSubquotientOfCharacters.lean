module

public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsSubquotientDetRepParInd
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsIrreducibleIffOfLinearEquiv
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
import Mathlib.RingTheory.Coalgebra.CoassocSimps
public import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsLocallyConstantOrbit
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LeviEmbMulSingle

@[expose] public section

noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.InertSupp ValuativeRel Matrix MeasureTheory
open GlobalTheory.IwahoriInj (Deep)
open scoped TensorProduct

namespace GlobalTheory.PrinProd

theorem isSubquotient_prinSeries_multiProd (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (N : ℕ) (χ : Fin N → kˣ →* ℂˣ) :
    IsSubquotient (prinSeries χ)
      (multiProd (Equiv.sigmaUnique (Fin N) fun _ => Fin 1) fun i => detRep (Fin 1) (χ i)) := by
  let e : (Σ _ : Fin N, Fin 1) ≃ Fin N := Equiv.sigmaUnique (Fin N) fun _ => Fin 1
  let κ : ℂ ≃ₗ[ℂ] ⨂[ℂ] _ : Fin N, ℂ := (PiTensorProduct.constantBaseRingEquiv (Fin N) ℂ).toLinearEquiv.symm
  let Ψ : IndSp (points (Fin N)) ((ofChar (torusChar χ)).comp (leviTorus k (Fin N)).symm.toMonoidHom) →ₗ[ℂ]
      IndSp e (piTensor fun i => detRep (Fin 1) (χ i)) :=
    MultiIrr.indPull (MonoidHom.id _) continuous_id κ.toLinearMap fun p =>
      ⟨⟨p, mem_parab_iff.2 fun a b _ _ hab => mem_parab_iff.1 p.2 a b 0 0 hab⟩, rfl, fun w => by
        have hd : ∀ a, GeneralLinearGroup.det (leviProj k e p a) =
            GeneralLinearGroup.det (leviProj k (points (Fin N))
              ⟨p, mem_parab_iff.2 fun a b _ _ hab => mem_parab_iff.1 p.2 a b 0 0 hab⟩ a) := fun a => by
          ext
          simp only [GeneralLinearGroup.val_det_apply, det_unique]
          rfl
        show (deltaHalf k _ (leviProj k e p) : ℂ) • piTensor (fun i => detRep (Fin 1) (χ i)) (leviProj k e p) (κ w) =
          κ ((deltaHalf k _ (leviProj k (points (Fin N)) _) : ℂ) •
            ofChar (torusChar χ) ((leviTorus k (Fin N)).symm (leviProj k (points (Fin N)) _)) w)
        rw [map_smul, deltaHalf_apply, deltaHalf_apply]
        refine congrArg₂ (fun (c : ℂˣ) (v : ⨂[ℂ] _ : Fin N, ℂ) => (c : ℂ) • v) ?_ ?_
        · refine (Finset.prod_congr rfl fun a _ => ?_)
          rw [hd, modExp_fin _ (fun _ => by simp), modExp_fin _ (fun _ => by simp)]
        · have hκ : ∀ w, κ w = w • PiTensorProduct.tprod ℂ (fun _ : Fin N => (1 : ℂ)) := fun w => by
            apply κ.symm.injective
            simp [κ]
          rw [hκ, hκ, map_smul, piTensor_tprod, ofChar_apply, torusChar_apply]
          have : (fun i => detRep (Fin 1) (χ i) (leviProj k e p i) 1) =
              fun i => (χ i (GeneralLinearGroup.det (leviProj k e p i)) : ℂ) • (1 : ℂ) := by
            funext i
            simp [detRep]
          rw [this, MultilinearMap.map_smul_univ, smul_smul, mul_comm, Units.coe_prod]
          simp only [hd]
          rfl⟩
  refine .of_injective ⟨Ψ, fun g => rfl⟩ fun f f' h => ?_
  exact Subtype.ext (Subtype.ext (funext fun x =>
    κ.injective (congrFun (congrArg (fun φ => φ.1.1) h) x)))

end GlobalTheory.PrinProd
