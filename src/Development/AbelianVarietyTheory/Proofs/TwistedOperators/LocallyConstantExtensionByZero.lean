module

public import Development.AbelianVarietyTheory.Definitions.Foundations.MatrixMeasurableSpace
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
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
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
import Development.AbelianVarietyTheory.Definitions.Foundations.SmoothPartStable
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.LeviEmbMemNormalizerLower

@[expose] public section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL Matrix Topology

noncomputable section
namespace GlobalTheory.SBExtend

variable {X : Type} [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X]
  [TotallyDisconnectedSpace X]


open Matrix Topology in
variable {X : Type} [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X]
  [TotallyDisconnectedSpace X] in
theorem _root_.GlobalTheory.SBExtend.exists_isCompact_isClopen_between {K W : Set X} (hK : IsCompact K)
    (hW : IsOpen W) (hKW : K ⊆ W) : ∃ V : Set X, IsCompact V ∧ IsClopen V ∧ K ⊆ V ∧ V ⊆ W := by
  have hB := loc_compact_Haus_tot_disc_of_zero_dim (X := X)
  have h : ∀ x ∈ K, ∃ U : Set X, (IsClopen U ∧ IsCompact U) ∧ x ∈ U ∧ U ⊆ W := by
    intro x hx
    obtain ⟨C, hCx, hCW, hC⟩ := local_compact_nhds (hW.mem_nhds (hKW hx))
    obtain ⟨U, hU, hxU, hUC⟩ :=
      hB.exists_subset_of_mem_open (mem_interior_iff_mem_nhds.2 hCx) isOpen_interior
    exact ⟨U, ⟨hU, hC.of_isClosed_subset hU.isClosed (hUC.trans interior_subset)⟩, hxU,
      (hUC.trans interior_subset).trans hCW⟩
  choose U hU hxU hUW using h
  obtain ⟨t, ht⟩ := hK.elim_nhds_subcover' U fun x hx => (hU x hx).1.isOpen.mem_nhds (hxU x hx)
  exact ⟨⋃ x ∈ t, U x x.2, t.isCompact_biUnion fun x _ => (hU x x.2).2,
    isClopen_biUnion_finset fun x _ => (hU x x.2).1, ht, Set.iUnion₂_subset fun x _ => hUW x x.2⟩


open Matrix Topology in
variable {X : Type} [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X]
  [TotallyDisconnectedSpace X] in
omit [LocallyCompactSpace X] [TotallyDisconnectedSpace X] in
theorem _root_.GlobalTheory.SBExtend.indicator_mem_SB {V : Set X} (hc : IsCompact V)
    (hV : IsClopen V) : (V.indicator fun _ => (1 : ℂ)) ∈ _root_.GlobalTheory.SplitWeil.SB X := by
  show IsLocallyConstant _ ∧ HasCompactSupport _
  refine ⟨fun s => ?_, HasCompactSupport.intro hc fun x hx => Set.indicator_of_notMem hx _⟩
  rcases Set.indicator_const_preimage V s (1 : ℂ) with h | h | h | h <;> rw [h]
  exacts [isOpen_univ, hV.isOpen, hV.compl.isOpen, isOpen_empty]

end GlobalTheory.SBExtend
