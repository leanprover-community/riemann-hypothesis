module

public import Mathlib.GroupTheory.Index
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
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NoTowerQ
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
import GroundTheory.LocalFields.Interface

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.Loc ValuativeRel GroundTheory.LocalField GlobalTheory.PMon.Ram

namespace GlobalTheory.PMon.Ram

theorem card_le_index_mul_card_map_inf (G H : Type) [Group G] [Group H] [Finite H]
    (f : G →* H) (N : Subgroup G) (I : Subgroup H) (hf : Function.Surjective f)
    (hN : N.index ≠ 0) : Nat.card ↥I ≤ N.index * Nat.card ↥(N.map f ⊓ I) := by
  have h1 : (N.map f).relIndex I * Nat.card ↥(N.map f ⊓ I) = Nat.card I := by
    rw [Subgroup.relIndex, mul_comm, ← Subgroup.card_mul_index ((N.map f).subgroupOf I)]
    congr 1
    rw [← Subgroup.inf_subgroupOf_right]
    exact (Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_right).toEquiv).symm
  have h2 : (N.map f).relIndex I ≤ (N.map f).index := by
    rw [← Subgroup.relIndex_top_right]
    apply Subgroup.relIndex_le_of_le_right le_top
    rw [Subgroup.relIndex_top_right]
    exact Subgroup.index_ne_zero_of_finite
  have h3 : (N.map f).index ≤ N.index :=
    Nat.le_of_dvd (Nat.pos_of_ne_zero hN) (Subgroup.index_map_dvd N hf)
  rw [← h1]
  exact Nat.mul_le_mul_right _ (h2.trans h3)

end GlobalTheory.PMon.Ram
