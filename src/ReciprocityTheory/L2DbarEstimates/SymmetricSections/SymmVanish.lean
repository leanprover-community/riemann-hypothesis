module

public import ReciprocityTheory.L2DbarEstimates.SymmetricSections.HoloSectionStatement
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import ReciprocityTheory.L2DbarEstimates.SymmetricSections.Sheets

@[expose] public section

namespace ReciprocityTheory.L2DbarEstimates.Norm

open Filter Topology Asymptotics

universe u

theorem symmVanish : symmVanishStatement.{u} := by
  intro n M _ z U u w₀ N hcov hw₀ hfin hvan k
  obtain ⟨W, d, s, hW, hwW, hcont, hzs, hvals⟩ := sheets n M z U u hcov w₀ hw₀ hfin
  have hWn : W ∈ 𝓝 w₀ := hW.mem_nhds hwW
  have hi : ∀ i, (fun v => u (s i v)) =O[𝓝 w₀] fun v => ‖v - w₀‖ ^ N := by
    intro i
    have hx : z (s i w₀) = w₀ := hzs i w₀ hwW
    have h1 := IsBigO.comp_tendsto (hvan (s i w₀) hx) ((hcont i).continuousAt hWn)
    refine h1.congr' (Eventually.of_forall fun v => rfl) ?_
    filter_upwards [hWn] with v hv
    simp only [Function.comp_apply, hzs i v hv, hx]
  have hprod : ∀ t : Finset (Fin d),
      (fun v => ∏ i ∈ t, u (s i v)) =O[𝓝 w₀] fun v => ‖v - w₀‖ ^ (t.card * N) := by
    intro t
    induction t using Finset.induction_on with
    | empty => simpa using (isBigO_const_const (1 : ℂ) (one_ne_zero : (1 : ℝ) ≠ 0) (𝓝 w₀))
    | insert a t ha ih =>
      have hc : (insert a t).card = t.card + 1 := by
        exact Finset.card_insert_of_notMem ha
      simp only [Finset.prod_insert ha]
      rw [hc]
      exact ((hi a).mul ih).congr' (Eventually.of_forall fun v => rfl)
        (Eventually.of_forall fun v => by
          show ‖v - w₀‖ ^ N * ‖v - w₀‖ ^ (t.card * N) = ‖v - w₀‖ ^ ((t.card + 1) * N)
          rw [← pow_add]; congr 1; ring)
  have heq : (fun v => ∑ t ∈ (Finset.univ : Finset (Fin d)).powersetCard k, ∏ i ∈ t, u (s i v))
      =ᶠ[𝓝 w₀] fiberSymm n z u k := by
    filter_upwards [hWn] with v hv
    rw [fiberSymm, hvals v hv, Finset.esymm_map_val]
  refine IsBigO.congr' ?_ heq (Eventually.of_forall fun _ => rfl)
  refine IsBigO.fun_sum fun t ht => ?_
  have := hprod t
  rwa [(Finset.mem_powersetCard.mp ht).2] at this

end ReciprocityTheory.L2DbarEstimates.Norm
