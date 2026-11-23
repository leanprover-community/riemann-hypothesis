module

public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsKodairaGeneric
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PConductor
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
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsKleimanScheme

@[expose] public section

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry GroundTheory.Heights₂.Heights.HilbertSamuel Filter Topology

namespace GlobalTheory.CompanionTheory.Conductor

theorem mem_chartRingQ_of_mem_chartRingZ {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
    {Ω : Type} [Field Ω] [CharZero Ω] (y : (Σ k, ι k) → Ω) (c : ∀ k, ι k) {x : Ω}
    (hx : x ∈ chartRingZ y c) : x ∈ chartRingQ y c := by
  unfold chartRingZ at hx
  unfold chartRingQ
  induction hx using Algebra.adjoin_induction with
  | mem z hz => exact Algebra.subset_adjoin hz
  | algebraMap r =>
    rw [eq_intCast (algebraMap ℤ Ω) r]
    exact intCast_mem _ r
  | add u v _ _ hu hv => exact add_mem hu hv
  | mul u v _ _ hu hv => exact mul_mem hu hv

theorem exists_conductor_section :
    ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] [CharZero Ω]
      (y : (Σ k, ι k) → Ω) (D : ℕ), IsArithVar (mCoordIdeal y) (D + 1) → Birational y →
      ∃ (e : K → ℕ) (c : Ω), c ≠ 0 ∧ ∀ (a : K → ℤ) (τ : ℕ),
        ∀ s ∈ Submodule.span ℚ (chartLatNm y a τ : Set Ω),
          c * s ∈ chartLatQ y ((τ : ℤ) • a + fun k => (e k : ℤ)) 1 := by
  classical
  intro K _ ι _ Ω _ _ y D _ hbir
  let C := {c : ∀ k, ι k // ∀ k, y ⟨k, c k⟩ ≠ 0}
  choose δ F hF hF0 hcond using fun c : C => Conductor.exists_chart_conductor y hbir c.1 c.2
  refine ⟨∑ c : C, δ c, ∏ c : C, aeval y (F c), Finset.prod_ne_zero_iff.mpr fun c _ => hF0 c,
    fun a τ s hs => ?_⟩
  have key : ∀ s ∈ chartLatNm y a τ, (∏ c : C, aeval y (F c)) * s ∈
      chartLatQ y ((τ : ℤ) • a + fun k => (((∑ c : C, δ c) k : ℕ) : ℤ)) 1 := by
    intro s hs c' hc'
    let c : C := ⟨c', hc'⟩
    have hx := hs c' hc'
    have hm : ∏ k, y ⟨k, c' k⟩ ^ (-(((1 : ℕ) : ℤ) *
          (((τ : ℤ) • a + fun k => (((∑ c : C, δ c) k : ℕ) : ℤ)) k))) =
        (∏ k, y ⟨k, c' k⟩ ^ (-((τ : ℤ) * a k))) * Conductor.invMon y c' (∑ c : C, δ c) := by
      rw [← Conductor.prod_zpow_eq_invMon, ← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun k _ => ?_
      rw [← zpow_add₀ (hc' k)]
      congr 1
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Nat.cast_one, one_mul]
      ring
    apply mem_chartRingQ_of_mem_chartRingZ
    rw [hm, ← Conductor.invMon_sum y c' Finset.univ δ]
    have hsplit : (∏ b : C, aeval y (F b)) * s * ((∏ k, y ⟨k, c' k⟩ ^ (-((τ : ℤ) * a k))) *
          ∏ b : C, Conductor.invMon y c' (δ b)) =
        (∏ b ∈ Finset.univ.erase c, aeval y (F b) * Conductor.invMon y c' (δ b)) *
          (aeval y (F c) * Conductor.invMon y c' (δ c) *
            (s * ∏ k, y ⟨k, c' k⟩ ^ (-((τ : ℤ) * a k)))) := by
      rw [← Finset.mul_prod_erase Finset.univ (fun b => aeval y (F b)) (Finset.mem_univ c),
        ← Finset.mul_prod_erase Finset.univ (fun b => Conductor.invMon y c' (δ b)) (Finset.mem_univ c),
        Finset.prod_mul_distrib]
      ring
    rw [hsplit]
    exact mul_mem (prod_mem fun b _ => Conductor.form_mul_invMon_mem y c' (hF b)) (hcond c _ hx)
  induction hs using Submodule.span_induction with
  | mem x hx => exact key x hx
  | zero => simpa using Submodule.zero_mem _
  | add u v _ _ hu hv => rw [mul_add]; exact Submodule.add_mem _ hu hv
  | smul r u _ hu => rw [mul_smul_comm]; exact Submodule.smul_mem _ r hu

end GlobalTheory.CompanionTheory.Conductor
