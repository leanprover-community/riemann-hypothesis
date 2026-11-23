module

public import Development.AbelianVarietyTheory.Definitions.Foundations.IsProbabilityMeasureMuPart
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.InterPolyProdSum
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
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsLieBase
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RootToFlag

@[expose] public section

open MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.GoodMetric GlobalTheory.LieBase GlobalTheory.GrassTop
open Classical

namespace GlobalTheory.GrassTop

theorem rootDiscr_isHomogeneous_sum {ι : Type} [Fintype ι] (m : ι → ℕ) :
    (rootDiscr m).IsHomogeneous (∑ τ, m τ * (m τ - 1) / 2) := by
  have h : (rootDiscr m).IsHomogeneous (∑ τ, ∑ j : Fin (m τ), ∑ _i ∈ Finset.Iio j, 1) := by
    unfold GlobalTheory.GoodMetric.rootDiscr
    refine IsHomogeneous.prod _ _ _ fun τ _ => ?_
    refine IsHomogeneous.prod _ _ _ fun j _ => ?_
    refine IsHomogeneous.prod _ _ _ fun i _ => ?_
    exact (isHomogeneous_X _ _).sub (isHomogeneous_X _ _)
  convert h using 1
  refine Finset.sum_congr rfl fun τ _ => ?_
  simp only [Finset.sum_const, smul_eq_mul, mul_one, Fin.card_Iio]
  rw [Fin.sum_univ_eq_sum_range (fun j => j) (m τ), Finset.sum_range_id]

theorem rootDiscr_isHomogeneous {E : Type} [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) :
    (rootDiscr Dw.mult).IsHomogeneous
      (Fintype.card (GlobalTheory.AllWt.Psi H) * (Dw.p * (Dw.p - 1) / 2 + Dw.q * (Dw.q - 1) / 2)) := by
  convert rootDiscr_isHomogeneous_sum Dw.mult using 1
  have hc : Fintype.card {τ : E →+* ℂ // ¬ τ (H.rt : E) = H.rt0} = Fintype.card (GlobalTheory.AllWt.Psi H) :=
    Fintype.card_congr
      { toFun := fun τ => ⟨conjEmb τ.1, GlobalTheory.AllWt.conj_mem τ.2⟩
        invFun := fun τ => ⟨conjEmb τ.1, GlobalTheory.AllWt.conj_not_mem τ⟩
        left_inv := fun τ => Subtype.ext (GlobalTheory.AllWt.conjEmb_conjEmb _)
        right_inv := fun τ => Subtype.ext (GlobalTheory.AllWt.conjEmb_conjEmb _) }
  have hp : Fintype.card (GlobalTheory.AllWt.Psi H) =
      (Finset.univ.filter fun τ : E →+* ℂ => τ (H.rt : E) = H.rt0).card := by
    rw [Fintype.card_subtype]
  have hq : Fintype.card (GlobalTheory.AllWt.Psi H) =
      (Finset.univ.filter fun τ : E →+* ℂ => ¬ τ (H.rt : E) = H.rt0).card := by
    rw [← hc, Fintype.card_subtype]
  have e : ∀ τ : E →+* ℂ, Dw.mult τ * (Dw.mult τ - 1) / 2 =
      if τ (H.rt : E) = H.rt0 then Dw.p * (Dw.p - 1) / 2 else Dw.q * (Dw.q - 1) / 2 := by
    intro τ; unfold Datum.mult; split_ifs <;> rfl
  simp only [e]
  rw [Finset.sum_ite, Finset.sum_const, Finset.sum_const, smul_eq_mul, smul_eq_mul, ← hp, ← hq]
  ring

end GlobalTheory.GrassTop
