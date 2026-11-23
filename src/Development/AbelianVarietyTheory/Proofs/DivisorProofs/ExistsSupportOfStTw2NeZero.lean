module

public import Development.AbelianVarietyTheory.Definitions.Divisors.SimpleTwistedTraceFormulaStable
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNeZeroOfTwOrbNeZero
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

open NumberField IsDedekindDomain Polynomial Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC
open scoped Classical TensorProduct
open GlobalTheory.BCT

noncomputable section

namespace GlobalTheory.BCT.GeoFin

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem ne_zero_of_finprod_mem_ne_zero {α : Type} (f : α → ℂ) (S : Set α) (hf : (Function.mulSupport f).Finite)
    (h : ∏ᶠ w ∈ S, f w ≠ 0) : ∀ w ∈ S, f w ≠ 0 := by
  intro w hw h0
  have hfin : (S ∩ Function.mulSupport f).Finite := hf.subset Set.inter_subset_right
  apply h
  rw [finprod_mem_eq_prod_of_inter_mulSupport_eq f (t := hfin.toFinset) (by
    ext x; simp only [Set.mem_inter_iff, Set.Finite.coe_toFinset]; tauto)]
  exact Finset.prod_eq_zero (i := w) (by simp [hw, h0]) h0

theorem exists_support_of_stTw2_ne_zero (a b : ℕ) (w : Pl E) (Q₁ Q₂ : (w.adicCompletion E)[X])
    (φ : GLw a w × GLw b w → ℂ) (h : stTw2 a b w Q₁ Q₂ φ ≠ 0) :
    ∃ y, φ y ≠ 0 ∧ (nrmL a w y.1).val.charpoly = Q₁ ∧ (nrmL b w y.2).val.charpoly = Q₂ := by
  obtain ⟨δ, ⟨hδ₁, hδ₂⟩, x, hx⟩ := exists_ne_zero_of_clSum_ne_zero
    ((thL a w).prodMap (thL b w))
    ((GlobalTheory.LFun.KGL w (n := a)).prod (GlobalTheory.LFun.KGL w (n := b)))
    {y | (nrmL a w y.1).val.charpoly = Q₁ ∧ (nrmL b w y.2).val.charpoly = Q₂} 1 φ h
  refine ⟨_, hx, ?_, ?_⟩
  · change (nrmL a w (x.1⁻¹ * δ.1 * thL a w x.1)).val.charpoly = Q₁
    rw [nrmL_twConj, ← hδ₁, Units.val_mul, Matrix.charpoly_mul_comm, ← Units.val_mul, mul_inv_cancel_left]
  · change (nrmL b w (x.2⁻¹ * δ.2 * thL b w x.2)).val.charpoly = Q₂
    rw [nrmL_twConj, ← hδ₂, Units.val_mul, Matrix.charpoly_mul_comm, ← Units.val_mul, mul_inv_cancel_left]

end GlobalTheory.BCT.GeoFin

namespace GlobalTheory.BCT.GeoFin

end GlobalTheory.BCT.GeoFin
