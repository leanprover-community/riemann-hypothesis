module

public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaCellCovers.KernelL2RowsColumns
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

open MeasureTheory
open scoped ENNReal Pointwise
open PositivityTheory.Rg.BcB.E1

namespace GlobalTheory.CompanionTheory.KernelCount

theorem cnt_ne_top (X : Ctx) (Ω : Set X.G) (hΩ : IsCompact Ω) (x : X.G) : cnt X.Γ Ω x ≠ ⊤ := by
  have hC : IsCompact ((fun z => x * z * x⁻¹) '' Ω) :=
    hΩ.image (by fun_prop)
  have hfin := X.proper _ hC
  have hsupp : (Function.support fun γ : X.Γ =>
      Ω.indicator (1 : X.G → ℝ≥0∞) (x⁻¹ * (γ : X.G) * x)) ⊆ (hfin.toFinset : Set X.Γ) := by
    intro γ hγ
    have hmem : x⁻¹ * (γ : X.G) * x ∈ Ω := by
      by_contra h
      exact hγ (Set.indicator_of_notMem h _)
    simp only [Set.Finite.coe_toFinset, Set.mem_ofPred_eq]
    exact ⟨_, hmem, by group⟩
  unfold cnt
  rw [tsum_eq_sum (s := hfin.toFinset) (fun γ hγ => by
    by_contra h
    exact hγ (by simpa using hsupp h))]
  refine (ENNReal.sum_lt_top.2 fun γ _ => ?_).ne
  refine lt_of_le_of_lt (Set.indicator_le_self' (fun _ _ => zero_le) _) ?_
  simp

theorem cnt_mul_left (X : Ctx) (Ω : Set X.G) (γ : X.G) (hγ : γ ∈ X.Γ) (x : X.G) :
    cnt X.Γ Ω (γ * x) = cnt X.Γ Ω x := by
  unfold cnt
  rw [← Equiv.tsum_eq (MulAut.conj (⟨γ, hγ⟩ : X.Γ)).toEquiv]
  refine tsum_congr fun δ => ?_
  have : (γ * x)⁻¹ * (((MulAut.conj (⟨γ, hγ⟩ : X.Γ)).toEquiv δ : X.Γ) : X.G) * (γ * x)
      = x⁻¹ * (δ : X.G) * x := by
    simp only [MulEquiv.toEquiv_eq_coe, EquivLike.coe_coe, MulAut.conj_apply, Subgroup.coe_mul,
      InvMemClass.coe_inv]
    group
  rw [this]

theorem cnt_mono (X : Ctx) {Ω Ω' : Set X.G} (h : Ω ⊆ Ω') (x : X.G) :
    cnt X.Γ Ω x ≤ cnt X.Γ Ω' x :=
  ENNReal.tsum_le_tsum fun _ => Set.indicator_le_indicator_of_subset h (fun _ => zero_le) _

theorem enorm_le_indicator {G : Type} [TopologicalSpace G] (φ : G → ℂ) (B : ℝ)
    (hB : ∀ z, ‖φ z‖ ≤ B) (z : G) :
    ‖φ z‖ₑ ≤ ENNReal.ofReal B * (tsupport φ).indicator (1 : G → ℝ≥0∞) z := by
  by_cases hz : z ∈ tsupport φ
  · rw [Set.indicator_of_mem hz, Pi.one_apply, mul_one, ← ofReal_norm]
    exact ENNReal.ofReal_le_ofReal (hB z)
  · rw [image_eq_zero_of_notMem_tsupport hz]
    simp

theorem cntBasic_of_kerBasic (h : KerBasic) : CntBasic := by
  intro X
  refine ⟨fun Ω hΩ x => cnt_ne_top X Ω hΩ x, fun Ω γ hγ x => cnt_mul_left X Ω γ hγ x,
    fun Ω Ω' hs x => cnt_mono X hs x, fun φ B hφ hB x => ?_⟩
  obtain ⟨-, -, -, -, -, hk⟩ := h X φ hφ
  refine (hk x x).trans ?_
  unfold cnt
  rw [← ENNReal.tsum_mul_left]
  exact ENNReal.tsum_le_tsum fun γ => enorm_le_indicator φ B hB _

end GlobalTheory.CompanionTheory.KernelCount

end
