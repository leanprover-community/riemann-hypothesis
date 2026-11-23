module

public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LocOf
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SameRowSameCosetScalarCorankOneStatement
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.FourierDecayAlt Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.SnFam
open scoped Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SnFamGen

theorem genFam : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word), (∀ t ∈ (Y.tO u u').genSet, ∀ t' ∈ (Y.tO u u').genSet, (Y.tO u u').rowOf t = (Y.tO u u').rowOf t' → (Y.tO u u').s0 t t' = 1 → (Y.tO u u').scal t t' → (Y.tO u u').s0 t' t = 1 ∧ (Y.tO u u').scal t' t) → (∀ t ∈ (Y.tO u u').genSet, ∀ t' ∈ (Y.tO u u').genSet, ∀ t'' ∈ (Y.tO u u').genSet, (Y.tO u u').rowOf t = (Y.tO u u').rowOf t' → (Y.tO u u').rowOf t' = (Y.tO u u').rowOf t'' → (Y.tO u u').s0 t t' = 1 → (Y.tO u u').scal t t' → (Y.tO u u').s0 t' t'' = 1 → (Y.tO u u').scal t' t'' → (Y.tO u u').s0 t t'' = 1 ∧ (Y.tO u u').scal t t'') → FamQ Y u u' Not (Y.tO u u').genSet (gCls Y u u') := by
  intro D X Y u u' hsym htr
  have hG : ∀ t : TauC Y u u', t ∈ (Y.tO u u').genSet → t.G ≠ 0 := by
    intro t ht h0
    have h1 : (Y.tO u u').G t ≠ 0 := ht.1
    apply h1
    show Gt t = 0
    simp [Gt, h0]
  have hrefl : ∀ t : TauC Y u u', t ∈ (Y.tO u u').genSet → t ∈ gCls Y u u' t := by
    intro t ht
    obtain ⟨h1, h2⟩ := GlobalTheory.T.same_row_same_coset_scalar_corank_one D X Y u u' t t (hG t ht) rfl rfl
    exact ⟨ht, rfl, h1, h2⟩

  have hrow : ∀ t t' : TauC Y u u', t' ∈ gCls Y u u' t → (Y.tO u u').rowOf t' = (Y.tO u u').rowOf t :=
    fun t t' h => h.2.1

  have hsub : ∀ t ∈ (Y.tO u u').genSet, ∀ t' ∈ (Y.tO u u').genSet,
      (Y.tO u u').rowOf t = (Y.tO u u').rowOf t' → (Y.tO u u').s0 t t' = 1 → (Y.tO u u').scal t t' →
      gCls Y u u' t' ⊆ gCls Y u u' t := by
    intro t ht t' ht' hr hs hc x hx
    obtain ⟨hxg, hxr, hxs, hxc⟩ := hx
    obtain ⟨h1, h2⟩ := htr t ht t' ht' x hxg hr hxr.symm hs hc hxs hxc
    exact ⟨hxg, hxr.trans hr.symm, h1, h2⟩
  refine ⟨?_, ?_, ?_⟩
  · ext t
    simp [setQ, Formalism.FourierDecayAlt.PB.Terms.genSet]
  · intro t ht t' ht' hn
    constructor
    · intro he
      have : t' ∈ gCls Y u u' t := he ▸ hrefl t' ht'
      exact (hrow t t' this).symm
    · intro hr
      obtain ⟨hs, hc⟩ := GlobalTheory.T.same_row_same_coset_scalar_corank_one D X Y u u' t t' (hG t ht) hr hn
      obtain ⟨hs', hc'⟩ := hsym t ht t' ht' hr hs hc
      exact Set.Subset.antisymm (hsub t' ht' t ht hr.symm hs' hc') (hsub t ht t' ht' hr hs hc)
  · intro t ht t' ht' he
    have : t' ∈ gCls Y u u' t := he ▸ hrefl t' ht'
    exact (hrow t t' this).symm

end GlobalTheory.SnFamGen
