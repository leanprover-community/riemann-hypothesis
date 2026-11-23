module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFockMap
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolEval
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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

open scoped TensorProduct Matrix Classical GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift

namespace GlobalTheory.CCRFock

theorem polMap_tprod_eq_prod_rename_mulX (W Λ : Type) [Fintype W] [DecidableEq W] (q : W → MvPolynomial Λ ℂ) :
    GlobalTheory.CCRFock.polMap W Λ (PiTensorProduct.tprod ℂ q) =
      ∏ v, MvPolynomial.rename (Prod.mk v) (q v) := by
  simp [GlobalTheory.CCRFock.polMap]

theorem polMap_comp_atPl_mulLeft_X : ∀ (W Λ : Type) [Fintype W] [DecidableEq W] (w : W) (l : Λ),
    GlobalTheory.CCRFock.polMap W Λ ∘ₗ GlobalTheory.RealLift.atPl (V := fun _ : W => MvPolynomial Λ ℂ) w
                 (LinearMap.mulLeft ℂ (MvPolynomial.X l)) =
      LinearMap.mulLeft ℂ (MvPolynomial.X (w, l)) ∘ₗ GlobalTheory.CCRFock.polMap W Λ := by
  intro W Λ _ _ w l
  apply PiTensorProduct.ext
  apply MultilinearMap.ext
  intro p
  have h : GlobalTheory.RealLift.atPl (V := fun _ : W => MvPolynomial Λ ℂ) w
        (LinearMap.mulLeft ℂ (MvPolynomial.X l)) (PiTensorProduct.tprod ℂ p) =
      PiTensorProduct.tprod ℂ (Function.update p w (MvPolynomial.X l * p w)) := by
    unfold GlobalTheory.RealLift.atPl
    rw [PiTensorProduct.map_tprod]
    congr 1
    funext v
    by_cases hv : v = w
    · subst hv; simp
    · simp [Function.update_of_ne hv]
  simp only [LinearMap.compMultilinearMap_apply, LinearMap.comp_apply, h, polMap_tprod_eq_prod_rename_mulX,
    LinearMap.mulLeft_apply]
  rw [Fintype.prod_eq_mul_prod_compl w, Fintype.prod_eq_mul_prod_compl w
    (fun v => MvPolynomial.rename (Prod.mk v) (p v)), ← mul_assoc]
  congr 1
  · simp
  · refine Finset.prod_congr rfl fun v hv => ?_
    have hv' : v ≠ w := by simpa using hv
    rw [Function.update_of_ne hv']

end GlobalTheory.CCRFock
