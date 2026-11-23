module

public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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

@[expose] public section

noncomputable section

namespace GlobalTheory.ExpAtTypePrimes

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G NumberField IsDedekindDomain

theorem col_smul {R : Ranks} {ι : Type} [Fintype ι] {hc : ι → HCParam R} (C : ColumnChain R ι hc) (a : ℂ)
    (φ : C.cls 0 → C.Y 0 → ℂ) : C.col (a • φ) = a • C.col φ := by
  unfold ColumnChain.col
  generalize R.m = n
  induction n with
  | zero => rfl
  | succ n ih =>
    funext j
    simp only [Formalism.ThetaLiftIndependence.chainOpM, Formalism.ThetaLiftIndependence.kerOpM, ih, Pi.smul_apply, map_smul, Finset.smul_sum]
    exact Finset.sum_congr rfl fun i _ => smul_comm _ _ _

theorem perCol_smul (D : D7) (u : D.what₂.Word) (μ : D.what₂.Tup) (a : ℂ) (φ : D.what₂.Mu u) (F : D.what₂.Amb μ) :
    D.what₂.perCol u μ (a • φ) F = a * D.what₂.perCol u μ φ F := by
  by_cases hμ : μ = D.what₂.mu0
  · subst hμ
    simp only [D.perCol_base_eq_PtilCol, PeriodMap.PtilCol, PeriodMap.Ptil, map_smul, Submodule.coe_smul, col_smul,
      LinearMap.smul_apply, smul_eq_mul]
  · simp only [D.perCol_tie u μ hμ, PeriodMap.PtilCol, PeriodMap.Ptil, map_smul, Submodule.coe_smul, col_smul,
      LinearMap.smul_apply, smul_eq_mul]

end GlobalTheory.ExpAtTypePrimes

end
