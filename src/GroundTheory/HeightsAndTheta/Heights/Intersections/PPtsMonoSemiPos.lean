module

public import GroundTheory.HeightsAndTheta.Heights.Intersections.StPtsMonoSemiPos
public import GroundTheory.HeightsAndTheta.Heights.Intersections.StSheetHessPSD
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
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
public import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.MdiscSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterBridgeA
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterFib

@[expose] public section

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo

theorem PtsMonoSemiPos.proof (hInt : PtsIntegrableStatement) (hHess : SheetHessPSD.Statement) :
    PtsMonoSemiPos.Statement := by
  intro K _ ι _ Q e M E D t hQ hMs hMp hE ht hD hDa hle
  classical
  unfold ptsIntegral
  by_cases hΨ : ∃ Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ), IsGoodProj Q Ψ
  swap
  · rw [dite_eq_right hΨ, dite_eq_right hΨ]
  rw [dite_eq_left hΨ, dite_eq_left hΨ]
  set Ψ := hΨ.choose with hΨdef
  have hΨg : IsGoodProj Q Ψ := hΨ.choose_spec
  unfold ptsIntegralAt
  have hD1 : IsSectionOn Q D 1 := by
    refine ⟨0, fun k => by simp [hDa], fun m hm k => ?_,
      fun h => hQ.2.1.1.ne_top ((Ideal.eq_top_iff_one Q).2 h)⟩
    rw [MvPolynomial.support_one, Finset.mem_singleton] at hm
    subst hm
    simp
  have key : ∀ y w, sheetDensity Q Ψ (pot M) (fun z => Real.log (D.h z)) y w =
      -sheetDensity Q Ψ (pot M) (logNorm D 1) y w := by
    intro y w
    unfold sheetDensity
    split_ifs <;> simp [logNorm, Real.log_inv]
  have h1 := hInt K ι Q e Ψ M E t hQ hΨg hMs hE ht
  have h2 : Integrable (fun y => ∑ᶠ w ∈ fibre Q Ψ y,
      sheetDensity Q Ψ (pot M) (fun z => Real.log (D.h z)) y w) := by
    simp only [key, finsum_neg_distrib]
    exact (hInt K ι Q e Ψ M D 1 hQ hΨg hMs hD hD1).neg
  obtain ⟨a, -, hta, htQ⟩ := ht
  have hJ : IsMultiHomogIdeal (Ideal.span {t}) :=
    ⟨{t}, fun f hf => ⟨a, (Set.mem_singleton_iff.mp hf) ▸ hta⟩, rfl⟩
  have hJQ : ¬ Ideal.span {t} ≤ Q := fun h => htQ (h (Ideal.subset_span rfl))
  have hnull := projB_null Ψ hQ hΨg hJ hJQ
  refine integral_mono_ae h1 h2 ?_
  rw [Filter.EventuallyLE, ae_iff]
  refine measure_mono_null (fun y hy => ?_) hnull
  by_contra hyB
  apply hy
  have hfin := fibreFinite K ι Q e Ψ hQ hΨg y
  rw [finsum_mem_eq_finite_toFinset_sum _ hfin, finsum_mem_eq_finite_toFinset_sum _ hfin]
  refine Finset.sum_le_sum fun w _ => ?_
  unfold sheetDensity
  by_cases hγ : ∃ γ, IsSheet Q Ψ y w γ
  · rw [dite_eq_left hγ, dite_eq_left hγ]
    obtain ⟨-, hev⟩ := hγ.choose_spec
    obtain ⟨-, hmem, hproj⟩ := hev.self_of_nhds
    have ht0 : eval (hγ.choose y) (map (Int.castRingHom ℂ) t) ≠ 0 := by
      intro h0
      refine hyB ⟨hγ.choose y, hmem, ⟨hmem.1, fun f hf => ?_⟩, hproj⟩
      obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp hf
      rw [map_mul, map_mul, h0, mul_zero]
    have hma : 0 ≤ maDensity (fun j y' => pot M j (hγ.choose y')) y :=
      ReciprocityTheory.AnForm.A.maDens_nonneg_of_posSemidef _ _ fun j =>
        hHess K ι Q e Ψ (M j) y w hγ.choose (hMs j) (hMp j) hγ.choose_spec
    exact mul_le_mul_of_nonneg_right (hle _ hmem ht0) hma
  · rw [dite_eq_right hγ, dite_eq_right hγ]

end GroundTheory.Heights₂.Heights.Inter
