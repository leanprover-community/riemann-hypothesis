module

public import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnifAt
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.LinearAlgebra.PiTensorProduct.Basis
import Mathlib.LinearAlgebra.PiTensorProduct.Finite
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.TotallySplit
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

@[expose] public section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct

noncomputable section

namespace GlobalTheory.BCT.TrKer

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

abbrev Wsp (lam : InfinitePlace E → DomWeight n) : Type :=
  PiTensorProduct ℂ fun v : InfinitePlace E => nablaSq ℂ n (lam v)

def wAt (lam : InfinitePlace E → DomWeight n) (γ : UE E n) : Wsp lam →ₗ[ℂ] Wsp lam :=
  PiTensorProduct.map fun v => GlobalTheory.Branching.sqRep ℂ n (lam v) (GeneralLinearGroup.map v.embedding γ.1)

def vecM (S : Set (Pl E)) (lam : InfinitePlace E → DomWeight n) (K' : ∀ w : Pl E, Subgroup (UL n w)) :
    Submodule ℂ (finU (E := E) (n := n) → Module.Dual ℂ (Wsp lam)) where
  carrier := {F | (∀ (γ : UE E n) x, F (finPt γ * x) = (wAt lam γ⁻¹).dualMap (F x)) ∧
    ∀ k ∈ globLev S K', ∀ x, F (x * k) = F x}
  add_mem' := by
    intro a b ha hb
    refine ⟨fun γ x => ?_, fun k hk x => ?_⟩
    · simp only [Pi.add_apply, ha.1 γ x, hb.1 γ x, map_add (f := _)]
    · simp only [Pi.add_apply, ha.2 k hk x, hb.2 k hk x]
  zero_mem' := ⟨fun _ _ => by simp, fun _ _ _ => rfl⟩
  smul_mem' := by
    intro c a ha
    refine ⟨fun γ x => ?_, fun k hk x => ?_⟩
    · simp only [Pi.smul_apply, ha.1 γ x, map_smul]
    · simp only [Pi.smul_apply, ha.2 k hk x]

def hopM (S : Set (Pl E)) (lam : InfinitePlace E → DomWeight n) (K' : ∀ w : Pl E, Subgroup (UL n w))
    (f : ∀ w : Pl E, UL n w → ℂ) :
    (finU (E := E) (n := n) → Module.Dual ℂ (Wsp lam)) →ₗ[ℂ] (finU (E := E) (n := n) → Module.Dual ℂ (Wsp lam)) :=
  levOp (rightReg ℂ (finU (E := E) (n := n)) (Module.Dual ℂ (Wsp lam))) (globLev S (KL n)) (globLev S K') (globFn S f)
    LinearMap.id

end GlobalTheory.BCT.TrKer

namespace GlobalTheory.BCT.TrKer

theorem trace_piMap {ι : Type} [Fintype ι] {M : ι → Type} [∀ c, AddCommGroup (M c)] [∀ c, Module ℂ (M c)]
    [∀ c, Module.Finite ℂ (M c)] (f : ∀ c, M c →ₗ[ℂ] M c) :
    LinearMap.trace ℂ (PiTensorProduct ℂ M) (PiTensorProduct.map f) =
      ∏ c, LinearMap.trace ℂ (M c) (f c) := by
  classical
  let bc := fun c => Module.Free.chooseBasis ℂ (M c)
  let B := Basis.piTensorProduct bc
  rw [LinearMap.trace_eq_matrix_trace ℂ B]
  have hc : ∀ c, LinearMap.trace ℂ (M c) (f c) = ∑ j, (bc c).repr (f c (bc c j)) j := by
    intro c
    rw [LinearMap.trace_eq_matrix_trace ℂ (bc c), Matrix.trace]
    simp only [Matrix.diag, LinearMap.toMatrix_apply]
  simp only [hc]
  rw [Fintype.prod_sum, Matrix.trace]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Matrix.diag, LinearMap.toMatrix_apply, Basis.piTensorProduct_apply, PiTensorProduct.map_tprod,
    Basis.piTensorProduct_repr_tprod_apply]

theorem finrank_wsp {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ} (lam : InfinitePlace E → DomWeight n) :
    (Module.finrank ℂ (Wsp lam) : ℂ) = dimW lam := by
  rw [← LinearMap.trace_id, ← PiTensorProduct.map_id, trace_piMap]
  unfold dimW
  simp

end GlobalTheory.BCT.TrKer
