module

public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DifferentiableSqTh
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.LatticeInvariantsPeriodPairDictionary
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.OddThetaFunctionExistenceUniqueness
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm

@[expose] public section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators

noncomputable section

namespace GlobalTheory.SigmaDuplication

open Filter Topology

theorem sgStar_two_mul {Λ : AddSubgroup ℂ} (hΛ : GlobalTheory.EvenTheta.IsLat Λ) {P : ℂ} (hP : P ∉ Λ) :
    sgStar Λ (2 * P) = -(wpD Λ P) * sgStar Λ P ^ 4 := by
  obtain ⟨⟨hdiff, hd0, -, -⟩, hzero, -, hwp, -⟩ := GlobalTheory.OddTheta.sgStar_laws Λ hΛ
  obtain ⟨L, hL⟩ := GlobalTheory.OddTheta.exists_periodPair Λ hΛ
  have h0 : sgStar Λ 0 = 0 := (hzero 0).2 (zero_mem Λ)
  have hPL : P ∉ L.lattice := fun hm => hP ((hL P).2 hm)
  have hwpfun : wpF Λ = L.weierstrassP := funext (GlobalTheory.OddTheta.wpF_eq L Λ hL)
  have hwpd : HasDerivAt (wpF Λ) (wpD Λ P) P := by
    rw [hwpfun, GlobalTheory.LatticeInvariants.wpD_eq hL P, ← congrFun L.deriv_weierstrassP P]
    exact ((L.differentiableOn_weierstrassP P hPL).differentiableAt
      (L.isClosed_lattice.isOpen_compl.mem_nhds hPL)).hasDerivAt
  have hA : HasDerivAt (fun v => sgStar Λ (P + v)) (deriv (sgStar Λ) (P + P) * 1) P :=
    (hdiff (P + P)).hasDerivAt.comp P ((hasDerivAt_id' P).const_add P)
  have hB : HasDerivAt (fun v => sgStar Λ (P - v)) (deriv (sgStar Λ) (P - P) * -1) P :=
    (hdiff (P - P)).hasDerivAt.comp P ((hasDerivAt_id' P).const_sub P)
  have hS := (hdiff P).hasDerivAt.pow 2
  have hG := (hwpd.sub_const (wpF Λ P)).mul (hS.const_mul (sgStar Λ P ^ 2))
  have hev : (fun v => sgStar Λ (P + v) * sgStar Λ (P - v)) =ᶠ[𝓝 P]
      (fun v => (wpF Λ v - wpF Λ P) * (sgStar Λ P ^ 2 * sgStar Λ v ^ 2)) := by
    have hne : sgStar Λ P ≠ 0 := fun h => hP ((hzero P).1 h)
    filter_upwards [(hdiff.continuous.continuousAt (x := P)).eventually_ne hne] with v hv
    have hvΛ : v ∉ Λ := fun hm => hv ((hzero v).2 hm)
    linear_combination hwp P v hP hvΛ
  have huniq := (hA.mul hB).unique (hG.congr_of_eventuallyEq hev)
  simp only [sub_self, h0, hd0, Pi.pow_apply] at huniq
  rw [two_mul]
  linear_combination -huniq

theorem U1_two_mul_at_zero_eq_neg_wpD_mul_pow_four : ∀ (Λ : AddSubgroup ℂ), GlobalTheory.EvenTheta.IsLat Λ → ∀ P : ℂ, P ∉ Λ →
    U1 Λ (2 * P) (sgStar Λ) 0 = -(wpD Λ P) * U1 Λ P (sgStar Λ) 0 ^ 4 := by
  intro Λ hΛ P hP
  show sgStar Λ (0 + 2 * P) * Complex.exp _ = -(wpD Λ P) * (sgStar Λ (0 + P) * Complex.exp _) ^ 4
  rw [zero_add, zero_add, sgStar_two_mul hΛ hP, mul_pow, ← Complex.exp_nat_mul, mul_assoc]
  congr 2
  simp only [map_mul, map_ofNat]
  push_cast
  ring_nf

end GlobalTheory.SigmaDuplication
