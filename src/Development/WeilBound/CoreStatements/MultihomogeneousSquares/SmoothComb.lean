module

public import Development.WeilBound.CoreStatements.MultihomogeneousSquares.AntisymmetryFibreSquares
public import Development.WeilBound.CoreStatements.FlagImmersions.SumFundOnRoot
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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

@[expose] public section

noncomputable section

namespace SquareStatements

open Filter Topology ReciprocityTheory.ChartRestriction.G.Geo GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top

theorem smooth_comb {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {J : Type} [Fintype J]
    (ℓ : J → HermLine ι) (n : J → ℤ) (h : ∀ j, IsSmoothHerm (ℓ j)) : IsSmoothHerm (Top.combLine ℓ n) := by
  show ContDiffOn ℝ _ (fun z => ∏ j, (ℓ j).h z ^ n j) _
  refine contDiffOn_prod fun j _ => ?_
  rcases n j with m | m
  · simpa using (h j).pow m
  · simp only [zpow_negSucc]
    exact ((h j).pow (m + 1)).inv fun z hz => (pow_pos ((ℓ j).pos z hz) _).ne'

theorem stXB : StX := by
  intro Ψ _ _ N K _ ι _ P e S Re sing h0 hd hc
  classical
  let cl : ℝ → ℝ := fun t => if 0 < t ∧ t ≤ S.t₀ then t else S.t₀
  have hcl : ∀ t, 0 < cl t ∧ cl t ≤ S.t₀ := fun t => by
    by_cases h : 0 < t ∧ t ≤ S.t₀
    · simp only [cl, if_pos h]; exact h
    · simp only [cl, if_neg h]; exact ⟨h0, le_rfl⟩
  refine ⟨fun t r => Top.combLine (fun a => Re.line a (cl t)) (Cmp.rootOnFund r), fun t r => ?_,
    fun t r => smooth_comb _ _ fun a => Re.line_smooth a _ (hcl t).1 (hcl t).2, fun t r z => ?_, ?_⟩
  · funext k
    have h1 : ∀ a, (Re.line a (cl t)).a k = -∑ m ∈ Finset.Iic a.2, (sing (a.1, m)).a k := fun a => by
      rw [Re.line_deg, hd]
      show (∑ r, _ • (sing r).a) k = _
      rw [RootFieldNumerics.Sq.sum_fundOnRoot]
      simp [Finset.sum_apply]
    have h2 := RootFieldNumerics.Sq.sum_root_fund r fun r' => ((sing r').a k : ℝ)
    show (∑ a, Cmp.rootOnFund r a • (Re.line a (cl t)).a) k = _
    rw [Finset.sum_apply]
    simp only [Pi.smul_apply, h1, smul_eq_mul]
    simp only [zsmul_eq_mul] at h2
    exact_mod_cast h2
  · show ∏ a, _ = ∏ a, _
    exact Finset.prod_congr rfl fun a _ => by rw [hc a (cl t) z]
  · filter_upwards [Ioo_mem_nhdsGT h0] with t ht r z _
    have : cl t = t := if_pos ⟨ht.1, ht.2.le⟩
    rw [this]

end SquareStatements
