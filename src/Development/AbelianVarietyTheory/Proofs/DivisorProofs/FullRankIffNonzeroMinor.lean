module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OmAOneApply
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.LeviEmbMemNormalizerLower
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FullRankSB

@[expose] public section

open Matrix MeasureTheory ValuativeRel GlobalTheory.SplitFlip GlobalTheory.SmGL GlobalTheory.WeilM GlobalTheory.RankFibre GlobalTheory.SplitWeil GlobalTheory.RankFibreKer

namespace GlobalTheory.RankFibreKer

theorem rank_eq_iff_exists_minor_ne_zero (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (a d : ℕ) (Y : Matrix (Fin a) (Fin d) k) :
    Y.rank = a ↔ ∃ J, minor Y J ≠ 0 := by
  constructor
  · intro hr
    obtain ⟨κ, f, hinj, hspan, hli⟩ := exists_linearIndependent' k Y.col
    haveI : Finite κ := Finite.of_injective f hinj
    haveI : Fintype κ := Fintype.ofFinite κ
    have hcard : Fintype.card κ = a := by
      rw [← finrank_span_eq_card hli, hspan, Matrix.finrank_span_range_col, hr]
    let e : κ ≃ Fin a := Fintype.equivFinOfCardEq hcard
    let J : Fin a ↪ Fin d := ⟨f ∘ e.symm, hinj.comp e.symm.injective⟩
    refine ⟨J, ?_⟩
    have hc : (Y.submatrix id J).col = (Y.col ∘ f) ∘ e.symm := by
      funext j i; rfl
    have hli' : LinearIndependent k (Y.submatrix id J).col := by
      rw [hc]; exact hli.comp e.symm e.symm.injective
    have hu := Matrix.linearIndependent_cols_iff_isUnit.mp hli'
    exact ((Matrix.isUnit_iff_isUnit_det _).mp hu).ne_zero
  · rintro ⟨J, hJ⟩
    have hu : IsUnit (Y.submatrix id J) := (Matrix.isUnit_iff_isUnit_det _).mpr (Ne.isUnit hJ)
    have hli' := Matrix.linearIndependent_rows_iff_isUnit.mpr hu
    have hr : (Y.submatrix id J).row = (LinearMap.funLeft k k J) ∘ Y.row := by
      funext i j; rfl
    rw [hr] at hli'
    have hli := LinearIndependent.of_comp _ hli'
    rw [Matrix.rank_eq_finrank_span_row, finrank_span_eq_card hli, Fintype.card_fin]

end GlobalTheory.RankFibreKer
