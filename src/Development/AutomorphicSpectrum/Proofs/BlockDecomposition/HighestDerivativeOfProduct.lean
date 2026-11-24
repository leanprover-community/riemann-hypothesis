module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ParabolicProductTwoRepsEquivTwoBlockInduction
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsIrreducibleIffOfLinearEquiv
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.LeibnizDerivatives.EPGFalseEqLastIff
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivMultiProdOne
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
import Mathlib.Topology.Sheaves.Init
import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.LeibnizOrders.ProdGPn

@[expose] public section

noncomputable section

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.HighestDeriv

section Coinv

variable {G V W : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

end Coinv

def piFinTwoTensor (X : Fin 2 → Type) [∀ a, AddCommGroup (X a)] [∀ a, Module ℂ (X a)] :
    (⨂[ℂ] a, X a) ≃ₗ[ℂ] X 0 ⊗[ℂ] X 1 :=
  ((LinearEquiv.lTensor _ (PiTensorProduct.subsingletonEquiv (s := fun i : Fin 1 => X i.succ) 0).symm).trans
    (GlobalTheory.SmGL.MultiIrr.tensorCons X)).symm

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

section Two

variable {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] {r t : ℕ}

def piTensorTwoEquiv' (π₁ : Representation ℂ (GL (Fin r) k) V) (π₂ : Representation ℂ (GL (Fin t) k) W) :
    (piTensor (GlobalTheory.BZMir.Leib.twoRep (k := k) π₁ π₂)).Equiv
      ((extTensor π₁ π₂).comp (leviTwo k (Fin r) (Fin t)).symm.toMonoidHom) :=
  .mk (GlobalTheory.SmGL.Exponents.boolTensorEquiv (X := TwoT V W)) fun g => by
    refine PiTensorProduct.ext (MultilinearMap.ext fun x => ?_)
    show GlobalTheory.SmGL.Exponents.boolTensorEquiv (X := TwoT V W)
        (piTensor (GlobalTheory.BZMir.Leib.twoRep (k := k) π₁ π₂) g (PiTensorProduct.tprod ℂ x)) =
      extTensor π₁ π₂ ((leviTwo k (Fin r) (Fin t)).symm g)
        (GlobalTheory.SmGL.Exponents.boolTensorEquiv (X := TwoT V W) (PiTensorProduct.tprod ℂ x))
    rw [piTensor_tprod, GlobalTheory.SmGL.Exponents.boolTensorEquiv_tprod, GlobalTheory.SmGL.Exponents.boolTensorEquiv_tprod]
    exact (extTensor_tmul π₁ π₂ ((leviTwo k (Fin r) (Fin t)).symm g) (x false) (x true)).symm

theorem nonempty_prod2_equiv (π₁ : Representation ℂ (GL (Fin r) k) V) (π₂ : Representation ℂ (GL (Fin t) k) W) :
    Nonempty ((prod2 (k := k) rfl π₁ π₂).Equiv (prod₂ π₁ π₂)) :=
  ⟨LocGL.parIndEquiv (two (stdSum (rfl : r + t = r + t))) (piTensorTwoEquiv' π₁ π₂)⟩

end Two

section Main

end Main

end GlobalTheory.CompanionTheory.HighestDeriv

end
