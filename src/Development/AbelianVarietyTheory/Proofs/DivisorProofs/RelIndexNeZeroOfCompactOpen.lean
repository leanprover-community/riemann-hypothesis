module

public import Mathlib.GroupTheory.Index
public import Mathlib.Topology.Algebra.Group.Defs
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
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.PointSide
public import Mathlib.Topology.Algebra.OpenSubgroup

@[expose] public section

open GlobalTheory.LKCount
open scoped Classical

namespace GlobalTheory.RelIndexCompact

theorem relIndex_ne_zero_of_compact_open {G : Type} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] {K L : Subgroup G} (hL : IsCompact (L : Set G))
    (hK : IsOpen (K : Set G)) : K.relIndex L ≠ 0 := by
  have : CompactSpace L := isCompact_iff_compactSpace.mp hL
  have ho : IsOpen ((K.subgroupOf L : Subgroup L) : Set L) := hK.preimage continuous_subtype_val
  have := Subgroup.quotient_finite_of_isOpen _ ho
  exact Subgroup.index_ne_zero_of_finite

theorem conj_map_isCompact_isOpen {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (K : Subgroup G) (x : G) (hK : IsCompact (K : Set G)) (ho : IsOpen (K : Set G)) :
    IsCompact ((K.map (MulAut.conj x).toMonoidHom : Subgroup G) : Set G) ∧
      IsOpen ((K.map (MulAut.conj x).toMonoidHom : Subgroup G) : Set G) := by
  rw [Subgroup.coe_map]
  have hc : Continuous (fun g : G => x * g * x⁻¹) := by fun_prop
  refine ⟨hK.image hc, ?_⟩
  have : ((MulAut.conj x).toMonoidHom : G → G) '' (K : Set G) =
      (fun g : G => x⁻¹ * g * x) ⁻¹' (K : Set G) := by
    ext y; simp [MulAut.conj_apply]
    constructor
    · rintro ⟨a, ha, rfl⟩; simpa [mul_assoc] using ha
    · intro hy; exact ⟨x⁻¹ * y * x, hy, by group⟩
  rw [this]; exact ho.preimage (by fun_prop)

end GlobalTheory.RelIndexCompact
