module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.ProfDefs
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
import Mathlib.GroupTheory.Schreier
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
public import Mathlib.GroupTheory.Finiteness

@[expose] public section

open Filter UpperTheory.V.AlgebraTools
open scoped TensorProduct

theorem UpperTheory.V.AlgebraTools.TopFG.subgroup_quot :
    ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G], TopFG G →
      (∀ H : Subgroup G, IsOpen (H : Set G) → TopFG H) ∧
      (∀ (Z : Type) [Group Z] [TopologicalSpace Z] (f : G →* Z), Continuous f → Function.Surjective f → TopFG Z) := by
  intro G _ _ _ _ hG
  obtain ⟨s, hs, hden⟩ := hG
  refine ⟨?_, ?_⟩
  · intro H hH
    haveI : Finite (G ⧸ H) := H.quotient_finite_of_isOpen hH
    haveI : H.FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
    set D := Subgroup.closure s with hD
    haveI : Finite s := hs
    haveI : Group.FG D := inferInstance
    haveI : (H.subgroupOf D).FiniteIndex := inferInstance
    have hfg : Group.FG (H.subgroupOf D) := inferInstance
    obtain ⟨t, ht, htf⟩ := Group.fg_iff.mp hfg
    let φ : H.subgroupOf D →* H :=
      (D.subtype.comp (H.subgroupOf D).subtype).codRestrict H (fun x => x.2)
    refine ⟨φ '' t, htf.image _, ?_⟩
    unfold TopGen
    rw [← MonoidHom.map_closure, ht, ← MonoidHom.range_eq_map]
    rw [dense_iff_inter_open]
    intro U hU hUne
    have hVo : IsOpen ((Subtype.val : H → G) '' U) := hH.isOpenMap_subtype_val U hU
    obtain ⟨x, ⟨y, hyU, rfl⟩, hxD⟩ := hden.inter_open_nonempty _ hVo (hUne.image _)
    refine ⟨y, hyU, ⟨⟨y.1, hxD⟩, y.2⟩, ?_⟩
    rfl
  · intro Z _ _ f hf hsurj
    refine ⟨f '' s, hs.image _, ?_⟩
    unfold TopGen at hden ⊢
    rw [← MonoidHom.map_closure, Subgroup.coe_map]
    exact hsurj.denseRange.dense_image hf hden
