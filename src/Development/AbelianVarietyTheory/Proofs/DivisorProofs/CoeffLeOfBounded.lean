module

public import Development.AbelianVarietyTheory.Definitions.Divisors.JoinCastSucc
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogGaussAbsSupportFinite
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import ReciprocityTheory.SemistableReduction.TorusL2CauchyInequality
import Development.AbelianVarietyTheory.Definitions.Divisors.MemSubPtsCutBaseChangeIff
import Development.AbelianVarietyTheory.Definitions.Divisors.WellChosen

@[expose] public section

set_option autoImplicit false

noncomputable section

open NumberField MvPolynomial ReciprocityTheory.MultiplicativeHeights GlobalTheory.ChowHt GlobalTheory.Adelic GlobalTheory.HSCore GlobalTheory.HSChoice
open Polynomial (nthRootsFinset)
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)

namespace GlobalTheory.HSFloor

theorem coeff_le_of_bounded {E : Type} [Field E] {σ : Type} [Fintype σ] (k : MvPolynomial σ E)
    (s : E →+* ℂ) (B : ℝ) (hB : ∀ z : σ → ℂ, (∀ i, ‖z i‖ ≤ 1) → ‖eval₂ s z k‖ ≤ B) (m : σ →₀ ℕ) :
    ‖s (k.coeff m)‖ ≤ B := by

  obtain ⟨θ, hθ⟩ := (ReciprocityTheory.MultiplicativeHeights.Closed.torus_l2_cauchy_inequality σ (MvPolynomial.map s k)).2 m
  have hz : ∀ i, ‖ReciprocityTheory.MultiplicativeHeights.torusPoint θ i‖ ≤ 1 := by
    intro i
    simp [ReciprocityTheory.MultiplicativeHeights.torusPoint, Complex.norm_exp]
  rw [MvPolynomial.coeff_map, MvPolynomial.eval_map] at hθ
  exact hθ.trans (hB _ hz)

theorem floor : ∀ (E : Type) [Field E] [NumberField E] (σ : Type) [Fintype σ] (k : MvPolynomial σ E)
    (B : (E →+* ℂ) → ℝ), k ≠ 0 →
    (∀ (s : E →+* ℂ) (z : σ → ℂ), (∀ i, ‖z i‖ ≤ 1) → ‖eval₂ s z k‖ ≤ B s) →
    -mean E (fun s => Real.log (B s)) ≤ finPart k := by
  intro E _ _ σ _ k B hk hB
  obtain ⟨m, hm⟩ := MvPolynomial.ne_zero_iff.mp hk
  refine le_trans (b := -mean E (fun s => Real.log ‖s (k.coeff m)‖)) ?_
    ((GlobalTheory.HSFinPart.finPart_props E σ σ).2.2 k m hm)
  rw [neg_le_neg_iff]
  unfold mean
  gcongr with τ _

  have hpos : 0 < ‖τ (k.coeff m)‖ := norm_pos_iff.mpr ((map_ne_zero τ).mpr hm)
  exact Real.log_le_log hpos (coeff_le_of_bounded k τ (B τ) (hB τ) m)

end GlobalTheory.HSFloor
