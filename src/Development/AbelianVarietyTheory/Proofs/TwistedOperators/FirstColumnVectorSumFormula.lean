module

public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Data.Fintype.Basic
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsGivenStageEqOne
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsMatchOver
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.FormulaAt

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

namespace GlobalTheory.FirstRowDatum

private theorem prod_apply_update_eq_mul_prod_erase {ι : Type} [Fintype ι] [DecidableEq ι] {X : ι → Type}
    (F : ∀ i, X i → ℂ) (x : ∀ i, X i) (j : ι) (y : X j) :
    ∏ i, F i (Function.update x j y i) = F j y * ∏ i ∈ Finset.univ.erase j, F i (x i) := by
  rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ j)]
  simp only [Function.update_self]
  congr 1
  refine Finset.prod_congr rfl fun i hi => ?_
  rw [Function.update_of_ne (Finset.ne_of_mem_erase hi)]

private theorem sum_prod_ite_map_eq_zero_of_sum_prod_eq_zero {ι κ : Type} [Fintype ι] [DecidableEq ι] {X : ι → Type}
    (Tm : ∀ i, (X i → ℂ) →ₗ[ℂ] (X i → ℂ)) (S : Finset κ) (c : κ → ℂ) (Φ : κ → ∀ i, X i → ℂ)
    (h : ∀ x : ∀ i, X i, ∑ d ∈ S, c d * ∏ i, Φ d i (x i) = 0) (s : Finset ι) :
    ∀ x : ∀ i, X i, ∑ d ∈ S, c d * ∏ i, (if i ∈ s then Tm i (Φ d i) else Φ d i) (x i) = 0 := by
  induction s using Finset.induction_on with
  | empty => simpa using h
  | insert j s hj ih =>
    intro x

    have hg : (∑ d ∈ S, (c d * ∏ i ∈ Finset.univ.erase j,
        (if i ∈ s then Tm i (Φ d i) else Φ d i) (x i)) • Φ d j) = 0 := by
      funext y
      rw [Finset.sum_apply, Pi.zero_apply, ← ih (Function.update x j y)]
      refine Finset.sum_congr rfl fun d _ => ?_
      rw [prod_apply_update_eq_mul_prod_erase (fun i => if i ∈ s then Tm i (Φ d i) else Φ d i) x j y]
      simp only [Pi.smul_apply, smul_eq_mul, if_neg hj]
      ring

    have hT := congrArg (fun g => Tm j g (x j)) hg

    simp only [map_sum, map_smul, map_zero, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at hT
    rw [← hT]
    refine Finset.sum_congr rfl fun d _ => ?_
    rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ j)]
    have h2 : ∏ i ∈ Finset.univ.erase j, (if i ∈ insert j s then Tm i (Φ d i) else Φ d i) (x i) =
        ∏ i ∈ Finset.univ.erase j, (if i ∈ s then Tm i (Φ d i) else Φ d i) (x i) := by
      refine Finset.prod_congr rfl fun i hi => ?_
      have hij : i ≠ j := Finset.ne_of_mem_erase hi
      simp only [Finset.mem_insert, hij, false_or]
    rw [h2, if_pos (Finset.mem_insert_self j s)]
    ring

theorem sum_prod_map_eq_zero {ι κ : Type} [Fintype ι] [DecidableEq ι] {X : ι → Type}
    (Tm : ∀ i, (X i → ℂ) →ₗ[ℂ] (X i → ℂ)) (S : Finset κ) (c : κ → ℂ) (Φ : κ → ∀ i, X i → ℂ)
    (h : ∀ x : ∀ i, X i, ∑ d ∈ S, c d * ∏ i, Φ d i (x i) = 0) (x : ∀ i, X i) :
    ∑ d ∈ S, c d * ∏ i, Tm i (Φ d i) (x i) = 0 := by
  have := sum_prod_ite_map_eq_zero_of_sum_prod_eq_zero Tm S c Φ h Finset.univ x
  simpa using this

theorem sum_prod_map_eq_zero₂ {κ : Type} {m : ℕ} {X Y : Fin m → Type} (TX : ∀ j, (X j → ℂ) →ₗ[ℂ] (X j → ℂ))
    (TY : ∀ i, (Y i → ℂ) →ₗ[ℂ] (Y i → ℂ)) (S : Finset κ) (c : κ → ℂ) (Φ : κ → ∀ j, X j → ℂ) (Ψ : κ → ∀ i, Y i → ℂ)
    (h : ∀ (x : ∀ j, X j) (y : ∀ i, Y i), ∑ d ∈ S, c d * (∏ j, Φ d j (x j)) * ∏ i, Ψ d i (y i) = 0)
    (x : ∀ j, X j) (y : ∀ i, Y i) :
    ∑ d ∈ S, c d * (∏ j, TX j (Φ d j) (x j)) * ∏ i, TY i (Ψ d i) (y i) = 0 := by

  have hx : ∀ (y : ∀ i, Y i) (x : ∀ j, X j),
      ∑ d ∈ S, (c d * ∏ i, Ψ d i (y i)) * ∏ j, TX j (Φ d j) (x j) = 0 := by
    intro y
    refine sum_prod_map_eq_zero TX S (fun d => c d * ∏ i, Ψ d i (y i)) Φ (fun x => ?_)
    rw [← h x y]
    refine Finset.sum_congr rfl fun d _ => ?_
    ring

  have hy := sum_prod_map_eq_zero TY S (fun d => c d * ∏ j, TX j (Φ d j) (x j)) Ψ (fun y' => by
    rw [← hx y' x]
    exact Finset.sum_congr rfl fun d _ => by ring) y
  rw [← hy]


end GlobalTheory.FirstRowDatum

end
