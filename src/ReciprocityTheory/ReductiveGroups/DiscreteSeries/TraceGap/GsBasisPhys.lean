module

public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TensorRepresentations.LowFockC
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

noncomputable section

open Finset

namespace ReciprocityTheory.ChartRestriction.DS.TRGap

variable {n : ℕ}

def sModes (ε : Fin n → Bool) : Finset (Fin n × Fin n) :=
  univ.filter fun x : Fin n × Fin n => ε x.1 = true ∧ ε x.2 = false ∧ x.2 < x.1

def sDeg (ε : Fin n → Bool) : ℕ := (sModes ε).card

def sIdx (ε : Fin n → Bool) : Finset (Fin (n * n)) := (sModes ε).map finProdFinEquiv.toEmbedding

theorem sIdx_eq (ε : Fin n → Bool) : sIdx ε = (lowerWedgeAlt ε).1 := by
  ext m
  obtain ⟨x, rfl⟩ := finProdFinEquiv.surjective m
  rw [mem_lowerWedge_iff]
  simp [sIdx, sModes]

theorem gs_basis_deg (S : Finset (Fin (n * n))) : fockBasis n S ∈ ⋀[ℂ]^S.card (Fin n × Fin n → ℂ) := by
  have hb : fockBasis n S = ExteriorAlgebra.ιMulti ℂ S.card
      (((Pi.basisFun ℂ (Fin n × Fin n)).reindex finProdFinEquiv) ∘ S.orderEmbOfFin rfl) := by
    rw [fockBasis, ExteriorAlgebra.basis_apply]
    rfl
  rw [hb]
  exact ExteriorAlgebra.ιMulti_range ℂ S.card ⟨_, rfl⟩

theorem sDeg_eq_sum (ε : Fin n → Bool) :
    (sDeg ε : ℝ) = ∑ a ∈ plusIdx ε, (rhoHol ε - rhoN ε) a := by
  have h1 : ∀ a ∈ plusIdx ε, (rhoHol ε - rhoN ε) a =
      ((univ.filter fun b => ε b = false ∧ b < a).card : ℝ) := by
    intro a ha
    rw [lf_rhoHol_sub_rhoN, if_pos (by simpa [plusIdx] using ha)]
  rw [Finset.sum_congr rfl h1]
  unfold sDeg sModes
  simp only [Finset.card_filter, Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero, plusIdx,
    Finset.sum_filter]
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun i _ => ?_
  by_cases hi : ε i = true <;> simp [hi]

end ReciprocityTheory.ChartRestriction.DS.TRGap
