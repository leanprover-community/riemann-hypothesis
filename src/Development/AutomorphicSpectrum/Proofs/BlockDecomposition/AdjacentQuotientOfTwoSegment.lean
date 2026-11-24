module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivMultiProdOne
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.NotInSupportOfSubsingleton
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsIrreducibleSecondFactorOfIrreducibleProduct
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
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.MultiProdCompCongr

@[expose] public section

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.SplitWeil GlobalTheory.ProdReorder
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.AdjQuot

section Linear

theorem nontrivial_piTensorProduct {ι : Type} [Fintype ι] {X : ι → Type} [∀ a, AddCommGroup (X a)]
    [∀ a, Module ℂ (X a)] [∀ a, Nontrivial (X a)] : Nontrivial (PiTensorProduct ℂ X) := by
  classical
  choose v hv using fun a => exists_ne (0 : X a)
  have hex : ∀ a, ∃ φ : Module.Dual ℂ (X a), φ (v a) ≠ 0 := fun a => by
    by_contra hc
    push_neg at hc
    exact hv a ((Module.forall_dual_apply_eq_zero_iff ℂ (v a)).1 hc)
  choose φ hφ using hex
  let L := PiTensorProduct.lift ((MultilinearMap.mkPiAlgebra ℂ ι ℂ).compLinearMap φ)
  have h : L (PiTensorProduct.tprod ℂ v) ≠ 0 := by
    simp only [L, PiTensorProduct.lift.tprod, MultilinearMap.compLinearMap_apply,
      MultilinearMap.mkPiAlgebra_apply]
    exact Finset.prod_ne_zero_iff.2 fun a _ => hφ a
  exact ⟨PiTensorProduct.tprod ℂ v, 0, fun h0 => h (by rw [h0, map_zero])⟩

end Linear

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

section Induction

variable {α n : Type} {m : α → Type} [Fintype α] [LinearOrder α] [∀ a, Fintype (m a)]
  [∀ a, DecidableEq (m a)] [Fintype n] [DecidableEq n] {W W' : Type} [AddCommGroup W] [Module ℂ W]
  [AddCommGroup W'] [Module ℂ W']

theorem nontrivial_indSp (e : (Σ a, m a) ≃ n) {ρ : Representation ℂ (Levi k m) W} (hρ : IsSmooth ρ)
    [Nontrivial W] : Nontrivial (IndSp e ρ) := by
  obtain ⟨u, hu⟩ := exists_ne (0 : W)
  obtain ⟨f, hf, -⟩ := GlobalTheory.SmGL.ProdIrr.exists_indSp_apply_one e ρ hρ u
  exact ⟨f, 0, fun h => hu (by rw [← hf, h]; rfl)⟩

end Induction

theorem nontrivial_prodIrr {h N : ℕ} (x : Fin h → IrrGL (k := k)) (hd : ∑ a, (x a).1 = N) :
    Nontrivial (IndSp (stdBlocks (fun a => (x a).1) hd) (piTensor fun a => (x a).rep)) := by
  haveI : ∀ a, Nontrivial (x a).2.rep.V := fun a => GlobalTheory.SmGL.Model.nontrivial_of_isIrreducible (x a).2.rep.irr
  haveI := nontrivial_piTensorProduct (X := fun a => (x a).2.rep.V)
  exact nontrivial_indSp _ (isSmooth_piTensor fun a => (x a).2.rep.smooth)

section Two

variable {V U W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup U] [Module ℂ U] [AddCommGroup W] [Module ℂ W]
  {r t N : ℕ}

end Two

section Concat



end Concat

end GlobalTheory.CompanionTheory.AdjQuot
end
