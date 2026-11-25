module

import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.JacquetModuleInStagesRefinedBlocks
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.StandardMaximalParabolic
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
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

open MeasureTheory ValuativeRel GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.IndefiniteRowSideFullHecke.StandardMaximalParabolic

namespace GlobalTheory.RadRev

open Matrix

variable {R : Type} [CommRing R] {α β n : Type} {m : α → Type} {m' : β → Type}
  [Fintype α] [LinearOrder α] [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)]
  [Fintype β] [LinearOrder β] [∀ a, Fintype (m' a)] [∀ a, DecidableEq (m' a)]
  [Fintype n] [DecidableEq n]

theorem mem_unipRad_entries {e : (Σ a, m a) ≃ n} {g : GL n R} :
    g ∈ unipRad R e ↔ ∀ i j, ¬ blk e i < blk e j → (g : Matrix n n R) i j = (1 : Matrix n n R) i j := by
  first | exact _root_.GlobalTheory.JacStagesProof.mem_unipRad_iff_entries' | exact @_root_.GlobalTheory.JacStagesProof.mem_unipRad_iff_entries' | apply _root_.GlobalTheory.JacStagesProof.mem_unipRad_iff_entries' <;> assumption


omit [Fintype α] [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)] [Fintype β] [∀ a, Fintype (m' a)]
  [∀ a, DecidableEq (m' a)] in
theorem blk_lt_of_parab_le [Nontrivial R] {e : (Σ a, m a) ≃ n} {e' : (Σ a, m' a) ≃ n}
    (h : parab R e ≤ parab R e') {i j : n} (hij : blk e' j < blk e' i) : blk e j < blk e i := by
  have hne : i ≠ j := fun hh => (ne_of_lt hij) (by rw [hh])
  by_contra hc
  have hdet : IsUnit (Matrix.transvection i j (1 : R)).det := by
    rw [Matrix.det_transvection_of_ne _ _ hne]
    exact isUnit_one
  obtain ⟨t, ht⟩ : ∃ t : GL n R, (t : Matrix n n R) = Matrix.transvection i j (1 : R) :=
    ⟨Matrix.nonsingInvUnit _ hdet, rfl⟩
  have hent : ∀ k l, (t : Matrix n n R) k l = (1 : Matrix n n R) k l + if i = k ∧ j = l then 1 else 0 := by
    intro k l
    rw [ht]
    simp [Matrix.transvection, Matrix.single_apply]
  have hmem : t ∈ parab R e := by
    change (t : Matrix n n R).BlockTriangular (blk e)
    intro k l hkl
    have hkl' : k ≠ l := fun hh => (ne_of_lt hkl) (by rw [hh])
    rw [hent, Matrix.one_apply_ne hkl', zero_add, if_neg]
    rintro ⟨rfl, rfl⟩
    exact hc hkl
  have hzero : (t : Matrix n n R) i j = 0 := (h hmem) hij
  rw [hent, Matrix.one_apply_ne hne, zero_add, if_pos ⟨rfl, rfl⟩] at hzero
  exact one_ne_zero hzero

theorem unipRad_le_of_parab_le [Nontrivial R] {e : (Σ a, m a) ≃ n} {e' : (Σ a, m' a) ≃ n}
    (h : parab R e ≤ parab R e') : unipRad R e' ≤ unipRad R e := by
  intro g hg
  rw [mem_unipRad_entries] at hg ⊢
  intro i j hij
  exact hg i j (fun hlt => hij (blk_lt_of_parab_le h hlt))

theorem stdMaxRad_le_unipRad : ∀ (F : Type) [Field F] {r a b s : ℕ} (h : a + b = r) (d : Fin s → ℕ)
    (hd : ∑ i, d i = r),
    parab F (stdBlocks d hd) ≤ stdMaxParab F h → stdMaxRad F h ≤ unipRad F (stdBlocks d hd) := by
  intro F _ r a b s h d hd hle
  exact unipRad_le_of_parab_le hle

end GlobalTheory.RadRev
