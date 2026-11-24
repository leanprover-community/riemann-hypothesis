module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnipotentCorrectionU1.CoreStar
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.BetaSesquilinearity
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open Matrix
open scoped ComplexConjugate

noncomputable section

namespace PI.UnitaryCorollaryDerivatives

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.U

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

open Formalism.FourierDecayAlt.P.BetaSesquilinearity

theorem gfWB_of (h1 : GfPoly) (h2 : PolyB) (h3 : CompR) : GfWB := by
  intro k r z z' χε ε n hχ
  obtain ⟨hχs, hχd, -⟩ := hχ
  obtain ⟨hsmC, hwb⟩ :=
    h2 k r (2 * (r + 1)) (fun g => ((Gf k r z z' g : ℝ) : ℂ)) (h1 k r z z')
  have hsmR : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun g : B.Mat k r => Gf k r z z' g) := by
    have h := Complex.reCLM.contDiff.comp hsmC
    simpa [Function.comp_def] using h
  refine ⟨?_, ?_⟩
  · exact Complex.ofRealCLM.contDiff.comp (hχs.comp hsmR)
  · obtain ⟨C₀, hC₀⟩ := hwb n
    refine h3 k r (fun g => Gf k r z z' g) χε (fun _ => 2 * (r + 1)) n C₀ hsmR hχs hχd ?_
    intro u v hu hv hlen hne g hg
    have hb := hC₀ u v hu hv hlen g hg
    have h1g : 1 ≤ B.gN g := gN_ge_one hg
    have hexp : ((2 * (r + 1) : ℕ) : ℝ) + ((((u ++ v).map (fun _ => (0 : ℕ))).sum : ℕ) : ℝ) ≤
        ((((u ++ v).map (fun _ => 2 * (r + 1))).sum : ℕ) : ℝ) := by
      have hl : 1 ≤ (u ++ v).length := List.length_pos_iff.mpr hne
      simp only [List.map_const', List.sum_replicate, smul_eq_mul, mul_zero, Nat.cast_zero,
        add_zero]
      exact_mod_cast Nat.le_mul_of_pos_left _ hl
    have hpos : 0 < B.gN g ^ (((2 * (r + 1) : ℕ) : ℝ) +
        ((((u ++ v).map (fun _ => (0 : ℕ))).sum : ℕ) : ℝ)) :=
      Real.rpow_pos_of_pos (lt_of_lt_of_le one_pos h1g) _
    have hC : 0 ≤ C₀ := (mul_nonneg_iff_of_pos_right hpos).mp ((norm_nonneg _).trans hb)
    exact hb.trans (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le h1g hexp) hC)

end PI.UnitaryCorollaryDerivatives
