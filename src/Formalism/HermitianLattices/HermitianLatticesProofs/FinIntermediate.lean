module

public import Formalism.HermitianLattices.DefsCS
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

@[expose] public section

namespace Formalism.HermitianLatticesTheory

theorem finIntermediate : FinIntermediate := by
  intro W _ P Q hPQ hfin

  let f : AddSubgroup W → AddSubgroup (Q ⧸ P.addSubgroupOf Q) := fun M =>
    (M.addSubgroupOf Q).map (QuotientAddGroup.mk' (P.addSubgroupOf Q))
  haveI : Finite (AddSubgroup (Q ⧸ P.addSubgroupOf Q)) :=
    Finite.of_injective (β := Set (Q ⧸ P.addSubgroupOf Q))
      (fun H : AddSubgroup (Q ⧸ P.addSubgroupOf Q) => (H : Set (Q ⧸ P.addSubgroupOf Q)))
      SetLike.coe_injective
  refine Set.Finite.of_finite_image (f := f) (Set.toFinite _) ?_
  intro M hM N hN hMN
  have key : ∀ M : AddSubgroup W, P ≤ M → M ≤ Q →
      (f M).comap (QuotientAddGroup.mk' (P.addSubgroupOf Q)) = M.addSubgroupOf Q := by
    intro M hPM _
    simp only [f]
    rw [AddSubgroup.comap_map_eq, QuotientAddGroup.ker_mk']
    exact sup_eq_left.mpr fun x hx =>
      AddSubgroup.mem_addSubgroupOf.mpr (hPM (AddSubgroup.mem_addSubgroupOf.mp hx))
  have h1 : M.addSubgroupOf Q = N.addSubgroupOf Q := by
    rw [← key M hM.1 hM.2, ← key N hN.1 hN.2, hMN]
  have h2 : ∀ M : AddSubgroup W, M ≤ Q → (M.addSubgroupOf Q).map Q.subtype = M := by
    intro M hMQ
    rw [AddSubgroup.addSubgroupOf_map_subtype, inf_eq_left.mpr hMQ]
  rw [← h2 M hM.2, ← h2 N hN.2, h1]

end Formalism.HermitianLatticesTheory
