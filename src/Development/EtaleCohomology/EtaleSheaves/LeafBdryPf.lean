module

public import Development.EtaleCohomology.EtaleSheaves.LeafGeoCut
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Lemma
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.TypeStar

@[expose] public section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Set Order TopologicalSpace Topology

namespace LateralTheory.E.LeafBdryPf

def univIC (Y : Type*) [TopologicalSpace Y] [IrreducibleSpace Y] : IrreducibleCloseds Y where
  carrier := univ
  isIrreducible' := IrreducibleSpace.isIrreducible_univ Y
  isClosed' := isClosed_univ

lemma withBot_lt_of_add_one_le {a b : WithBot ℕ∞} (h : a + 1 ≤ b) (hb : b < ⊤) (ha : a ≠ ⊥) : a < b := by
  induction a using WithBot.recBotCoe with
  | bot => exact absurd rfl ha
  | coe a =>
    induction b using WithBot.recBotCoe with
    | bot => exact absurd h (by simp)
    | coe b =>
      have hb' : b < ⊤ := by
        rw [← WithBot.coe_top] at hb
        exact WithBot.coe_lt_coe.mp hb
      have h' : a + 1 ≤ b := by exact_mod_cast h
      have ha' : a ≠ ⊤ := (lt_of_le_of_lt (le_self_add.trans h') hb').ne
      exact WithBot.coe_lt_coe.mpr ((ENat.add_one_le_iff ha').mp h')

theorem dim_lt_of_closedEmbedding {Z Y : Type*} [TopologicalSpace Z] [TopologicalSpace Y] [IrreducibleSpace Y]
    (f : Z → Y) (hf : IsClosedEmbedding f) (hfin : topologicalKrullDim Y < ⊤) (hne : (range f)ᶜ.Nonempty) :
    topologicalKrullDim Z < topologicalKrullDim Y := by
  have hY : Nonempty (IrreducibleCloseds Y) := ⟨univIC Y⟩
  by_cases hZ : Nonempty (IrreducibleCloseds Z)
  · have hlt : ∀ c : IrreducibleCloseds Z, IrreducibleCloseds.map f hf.continuous c < univIC Y := by
      intro c
      refine lt_of_le_of_ne (fun x _ => trivial) ?_
      intro heq
      obtain ⟨y, hy⟩ := hne
      have h1 : (IrreducibleCloseds.map f hf.continuous c : Set Y) ⊆ range f := by
        rw [IrreducibleCloseds.coe_map]
        exact closure_minimal (image_subset_range _ _) hf.isClosed_range
      apply hy
      apply h1
      rw [heq]
      trivial
    let g : WithTop (IrreducibleCloseds Z) → IrreducibleCloseds Y :=
      fun o => WithTop.recTopCoe (univIC Y) (IrreducibleCloseds.map f hf.continuous) o
    have hg : StrictMono g := by
      intro a b hab
      induction a using WithTop.recTopCoe with
      | top => exact absurd hab (by simp)
      | coe a =>
        induction b using WithTop.recTopCoe with
        | top => exact hlt a
        | coe b =>
          exact IrreducibleCloseds.map_strictMono_of_isInducing hf.isInducing (WithTop.coe_lt_coe.mp hab)
    have h := krullDim_le_of_strictMono g hg
    rw [krullDim_WithTop] at h
    exact withBot_lt_of_add_one_le h hfin (bot_lt_krullDim).ne'
  · rw [not_nonempty_iff] at hZ
    have : topologicalKrullDim Z = ⊥ := krullDim_eq_bot
    rw [this]
    exact bot_lt_krullDim

theorem LeafBdry_of : LateralTheory.E.LeafGeoCut.LeafBdry := by
  intro Y B W p ι hι hirr hfin hne
  have : IsClosedImmersion (pullback.fst p ι) := inferInstance
  refine dim_lt_of_closedEmbedding _ (pullback.fst p ι).isClosedEmbedding hfin ?_
  rw [Scheme.Pullback.range_fst, ← preimage_compl]
  exact hne

end LateralTheory.E.LeafBdryPf

end
