module

import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeylProduct.WeylProd
public import Formalism.PeriodIntegrals.WeylForU
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Topology.Sheaves.Init
import Formalism.LocalRingCardinality.Params

@[expose] public section

noncomputable section

namespace PI.WeylForUWork

open Finset PI.UpqRep Formalism.BasicNotions

theorem denom_range (n : ℕ) :
    ∏ i ∈ range n, ∏ j ∈ Ico (i + 1) n, ((j : ℝ) - (i : ℝ)) =
      ∏ i ∈ range n, ((i.factorial : ℕ) : ℝ) := by
  apply PI.WeylProdWork.denom_eq <;> assumption

theorem row_fin (n : ℕ) (a : Fin n) :
    ∏ b ∈ univ.filter (fun b : Fin n => a < b), (((b : ℕ) : ℝ) - ((a : ℕ) : ℝ)) =
      ∏ j ∈ Ico ((a : ℕ) + 1) n, ((j : ℝ) - ((a : ℕ) : ℝ)) := by
  refine Finset.prod_nbij (fun b : Fin n => (b : ℕ)) ?_ ?_ ?_ ?_
  · intro b hb
    rw [Finset.mem_filter] at hb
    rw [Finset.mem_Ico]
    exact ⟨hb.2, b.isLt⟩
  · intro x _ y _ h
    exact Fin.ext h
  · intro j hj
    rw [Finset.mem_coe, Finset.mem_Ico] at hj
    refine ⟨⟨j, hj.2⟩, ?_, rfl⟩
    rw [Finset.mem_coe, Finset.mem_filter]
    exact ⟨Finset.mem_univ _, hj.1⟩
  · intro b _
    rfl

theorem denom_fin (n : ℕ) :
    ∏ a : Fin n, ∏ b ∈ univ.filter (fun b : Fin n => a < b), (((b : ℕ) : ℝ) - ((a : ℕ) : ℝ)) =
      ∏ i ∈ range n, ((i.factorial : ℕ) : ℝ) := by
  refine (Finset.prod_congr rfl (fun a _ => row_fin n a)).trans ?_
  exact (Fin.prod_univ_eq_prod_range (fun i : ℕ => ∏ j ∈ Ico (i + 1) n, ((j : ℝ) - (i : ℝ))) n).trans
    (denom_range n)

theorem natW_anti {N : ℕ} (lam : DomWeight N) : Antitone lam.natW :=
  fun _ _ hij => Int.toNat_le_toNat (sub_le_sub_right (lam.anti hij) _)

theorem natW_cast {N : ℕ} (lam : DomWeight N) (i : Fin N) :
    ((lam.natW i : ℕ) : ℤ) = lam.w i - lam.detShift := by
  have hN0 : 0 < N := Fin.pos i
  have hle : lam.w ⟨N - 1, by omega⟩ ≤ lam.w i :=
    lam.anti (Fin.le_iff_val_le_val.mpr (by simp only; omega))
  unfold DomWeight.natW DomWeight.detShift
  rw [dite_eq_left hN0]
  exact Int.toNat_of_nonneg (by omega)

theorem natW_cast_real {N : ℕ} (lam : DomWeight N) (i : Fin N) :
    ((lam.natW i : ℕ) : ℝ) = ((lam.w i : ℤ) : ℝ) - ((lam.detShift : ℤ) : ℝ) := by
  exact_mod_cast natW_cast lam i

theorem weylForU_of : PI.ModelIso → PI.NablaDim → PI.WeylForU := by
  intro hM hN N Λ H _ _ σ S hU hK
  obtain ⟨lam, hΛ, hdim⟩ := hM N Λ H σ S hU hK
  rw [hdim]
  have h2 : ((Module.finrank ℂ ↥(nablaSq ℂ N lam) : ℕ) : ℚ) =
      (∏ i : Fin N, ∏ j ∈ univ.filter (fun j : Fin N => i < j), (((lam.natW i : ℕ) : ℚ) -
        ((lam.natW j : ℕ) : ℚ) + ((j : ℕ) : ℚ) - ((i : ℕ) : ℚ))) /
      ∏ i : Fin N, ∏ j ∈ univ.filter (fun j : Fin N => i < j), (((j : ℕ) : ℚ) - ((i : ℕ) : ℚ)) := by
    rw [← Finset.prod_div_distrib]
    refine (hN N lam.natW (natW_anti lam)).trans (Finset.prod_congr rfl (fun i _ => ?_))
    rw [← Finset.prod_div_distrib, Finset.prod_filter]
  have h3 := congrArg (fun q : ℚ => (q : ℝ)) h2
  push_cast at h3
  rw [h3, denom_fin]
  congr 1
  refine Finset.prod_congr rfl (fun a _ => Finset.prod_congr rfl (fun b _ => ?_))
  rw [natW_cast_real, natW_cast_real, hΛ a, hΛ b]
  ring

end PI.WeylForUWork
