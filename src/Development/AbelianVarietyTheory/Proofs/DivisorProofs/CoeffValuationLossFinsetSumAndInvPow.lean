module

public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.InfClassAt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteInfiniteScalarBounds
public import Formalism.LocalToGlobal.ExponentGrids.ExponentGridsProofs.NormaliserValuationBound
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemVarLat

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.RowTest GlobalTheory.SumSize GlobalTheory.RowClaim
open Formalism.DivisionValues (vw lw)
open MeasureTheory ValuativeRel GlobalTheory.UnfoldLoss

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField GlobalTheory.FunObj.borelKw
  GlobalTheory.FunObj.borelSpaceKw

namespace GlobalTheory.LossSum

theorem lossLe_sum_and_pow : ∀ {D : D7} (w : PlL D),
    (∀ {ι : Type} (s : Finset ι) (z : ι → ℂ) (a : ℝ), (∀ i ∈ s, LossLe w (z i) a) → LossLe w (∑ i ∈ s, z i) a) ∧
    ∀ q M : ℕ, 0 < q → LossLe w ((((q : ℝ)⁻¹ ^ M : ℝ)) : ℂ) ((M : ℝ) * (vw w ((q : ℕ) : D.what₂.LL) : ℝ)) := by
  intro D w
  refine ⟨?_, ?_⟩
  · intro ι s z a h
    classical
    induction s using Finset.induction_on with
    | empty => exact ⟨0, by simp, Or.inl rfl⟩
    | insert j s hj ih =>
      rw [Finset.sum_insert hj]
      obtain ⟨y1, e1, h1⟩ := h j (Finset.mem_insert_self _ _)
      obtain ⟨y2, e2, h2⟩ := ih fun i hi => h i (Finset.mem_insert_of_mem hi)
      refine ⟨y1 + y2, by rw [map_add (f := _), e1, e2], ?_⟩
      by_cases hy1 : y1 = 0
      · subst hy1; simpa using h2
      by_cases hy2 : y2 = 0
      · subst hy2; simpa using h1
      have h1' := h1.resolve_left hy1
      have h2' := h2.resolve_left hy2
      by_cases h3 : y1 + y2 = 0
      · exact Or.inl h3
      right
      have h4 := Formalism.AtG.ValuationJets.vw_add w y1 y2 hy1 hy2 h3
      have h5 : ((min (vw w y1) (vw w y2) : ℤ) : ℝ) ≤ (vw w (y1 + y2) : ℝ) := by exact_mod_cast h4
      push_cast at h5
      exact le_trans (le_min h1' h2') h5
  · intro q M hq
    refine ⟨((q : D.what₂.LL)⁻¹) ^ M, by push_cast; simp, Or.inr ?_⟩
    have hq0 : ((q : D.what₂.LL)⁻¹) ≠ 0 := inv_ne_zero (by exact_mod_cast hq.ne')
    rw [GlobalTheory.ScalAA.vw_pow' w hq0, GlobalTheory.ScalAA.vw_inv']
    push_cast; ring_nf; rfl

end GlobalTheory.LossSum
