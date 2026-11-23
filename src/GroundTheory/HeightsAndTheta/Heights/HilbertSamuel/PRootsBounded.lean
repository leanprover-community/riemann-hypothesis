module

public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsRootsBounded
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
public import Mathlib.Analysis.Polynomial.CauchyBound
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
public import Mathlib.Topology.Algebra.MvPolynomial
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Algebra.Polynomial.Eval.Coeff
public import Mathlib.Algebra.Polynomial.Monic

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial Filter Topology NNReal

theorem RootsBounded.continuous_aeval {e : ℕ} (g : MvPolynomial (Fin e) ℚ) :
    Continuous fun y : Fin e → ℂ => aeval y g := by
  have h := MvPolynomial.continuous_eval (p := MvPolynomial.map (algebraMap ℚ ℂ) g)
  refine h.congr fun y => ?_
  rw [MvPolynomial.eval_map, MvPolynomial.aeval_def]

theorem RootsBounded.proof : RootsBounded.Statement := by
  intro e G hG y₀
  set m := G.natDegree
  let a : ℕ → (Fin e → ℂ) → ℂ := fun k y => aeval y (G.coeff k)
  refine ⟨((1 + ∑ k ∈ Finset.range m, (‖a k y₀‖₊ + 1) : ℝ≥0) : ℝ), ?_⟩
  have hev : ∀ᶠ y in 𝓝 y₀, ∀ k ∈ Finset.range m, ‖a k y‖₊ ≤ ‖a k y₀‖₊ + 1 := by
    rw [eventually_all_finset]
    intro k _
    have hc : Continuous fun y => ‖a k y‖₊ :=
      (RootsBounded.continuous_aeval (G.coeff k)).nnnorm
    exact hc.continuousAt.eventually (gt_mem_nhds (lt_add_one _)) |>.mono fun _ h => h.le
  filter_upwards [hev] with y hy t ht
  set P : Polynomial ℂ := G.map (aeval y).toRingHom
  have hPm : P.Monic := hG.map _
  have hdeg : P.natDegree = m := hG.natDegree_map _
  have hroot : P.IsRoot t := by
    rw [Polynomial.IsRoot, Polynomial.eval_map]; exact ht
  have hlt := Polynomial.IsRoot.norm_lt_cauchyBound hPm.ne_zero hroot
  have hcb : Polynomial.cauchyBound P ≤ 1 + ∑ k ∈ Finset.range m, (‖a k y₀‖₊ + 1) := by
    rw [Polynomial.cauchyBound, hPm.leadingCoeff, nnnorm_one, div_one, add_comm]
    gcongr
    rw [hdeg]
    refine Finset.sup_le fun k hk => ?_
    have hcoeff : P.coeff k = a k y := by
      simp [P, a, Polynomial.coeff_map]
    rw [hcoeff]
    exact (hy k hk).trans (Finset.single_le_sum (f := fun k => ‖a k y₀‖₊ + 1)
      (fun _ _ => bot_le) hk)
  have : ‖t‖₊ ≤ 1 + ∑ k ∈ Finset.range m, (‖a k y₀‖₊ + 1) := (hlt.trans_le hcb).le
  exact_mod_cast this

end GroundTheory.Heights₂.Heights.HilbertSamuel
