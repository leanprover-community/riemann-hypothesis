module

public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SelfIntersectionLowerHeight
public import Development.AbelianVarietyTheory.Definitions.Divisors.CharZeroFunctionField
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.SmallSecTensTriv
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmallSectionsTwistedPowerEncardEqBall
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.Basify

-- This file was produced by scripts/clump.py from the modules listed below.
-- Members: Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianLineBundleIsNefShiftMonotone, Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithHilbertSamuelLogBallCountTendsto

-- ===== clump member: Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianLineBundleIsNefShiftMonotone =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianLineBundleIsNefShiftMonotone", "h": "module\n\npublic import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift\npublic import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SelfIntersectionLowerHeight\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Algebra.Order.Star.Real\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Bernstein\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Data.Nat.Choose.Multinomial\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Development.AbelianVarietyTheory.Definitions.Divisors.CharZeroFunctionField\n\n"}
section -- clump:auto
@[expose] public section

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr

namespace GlobalTheory.NefShift

theorem isNef_shift_mono : GlobalTheory.Published.ArCalc → ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X]
    (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (M : HermLB p) (t t' : ℝ), t ≤ t' →
    (M.shift (fun _ => t) fun _ => rfl).IsNef D → (M.shift (fun _ => t') fun _ => rfl).IsNef D := by
  intro _ k _ X _ p D hX M t t' htt h
  refine ⟨fun σ => ?_, h.vertical, ?_⟩
  · have := (h.semiPos σ).addFn_const (2 * (t' - t))
    have e : (((M.shift (fun _ => t) fun _ => rfl).φ σ).addFn fun _ => 2 * (t' - t)) =
        (M.shift (fun _ => t') fun _ => rfl).φ σ := by
      simp only [HermLB.shift, Weight.addFn]
      congr 1
      funext a b
      ring
    exact e ▸ this
  · intro Z i _ _ _ hc hd
    obtain ⟨r, hr, h0⟩ := h.horizontal Z i hc hd
    refine ⟨r, hr, ?_⟩
    have e₁ := HtSelfInter.curveDeg_shift hX M t i hc hd (r := r) hr
    have e₂ := HtSelfInter.curveDeg_shift hX M t' i hc hd (r := r) hr
    rw [e₂]
    rw [e₁] at h0
    nlinarith [(Nat.cast_nonneg _ : (0:ℝ) ≤ Nat.card (X.residueField (i (genericPoint Z)) →+* ℂ))]

end GlobalTheory.NefShift
end -- clump:auto
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianLineBundleIsNefShiftMonotone =====

-- ===== clump member: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithHilbertSamuelLogBallCountTendsto =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithHilbertSamuelLogBallCountTendsto", "h": "module\n\npublic import Development.AbelianVarietyTheory.Definitions.Divisors.CharZeroFunctionField\npublic import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.SmallSecTensTriv\npublic import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift\npublic import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianLineBundleIsNefShiftMonotone\npublic import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmallSectionsTwistedPowerEncardEqBall\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Bernstein\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Data.Nat.Choose.Multinomial\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Basify\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\n\n"}
section -- clump:auto
@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr

namespace GlobalTheory.VolBr

theorem lc_tendsto_of_rep : GlobalTheory.Published.ArithHilbertSamuel → GlobalTheory.Published.ArCalc → ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (P : Pair p), ∀ (a b : ℤ) (M : HermLB p) (α t₀ : ℝ), P.Rep a b M → M.IsSelfInter α → (M.shift (fun _ => t₀) fun _ => rfl).IsNef D → ∀ t, t₀ ≤ t → Tendsto (fun m : ℕ => P.lc (m * a) (m * b) (Real.exp (t * m)) / (m : ℝ) ^ (D + 1)) atTop (𝓝 (α / (D + 1).factorial + ((D + 1) * gdeg M D / (D + 1).factorial) * t)) := by
  intro hHS hC k _ X _ p D hX P a b M α t₀ hRep hα hN t ht
  have hNt := _root_.GlobalTheory.NefShift.isNef_shift_mono hC k X p D hX M t₀ t ht hN
  have hSt := hC.arShift k X p D hX M α t hα
  have hT := GlobalTheory.Published.ArithHilbertSamuel.tendsto_of_triv hHS hX hNt hSt
  have hF : ((D + 1).factorial : ℝ) ≠ 0 := by positivity
  have h2 := hT.div_const ((D + 1).factorial : ℝ)
  have e (m : ℕ) : P.lc (m * a) (m * b) (Real.exp (t * m)) =
      Real.log ((((M.shift (fun _ => t) fun _ => rfl).pow m).smallSec.ncard : ℝ)) := by
    rw [Pair.lc, Set.ncard_def, Set.ncard_def, (_root_.GlobalTheory.VolBr.SmallBall.main k X p P a b M hRep t m).1]
  convert (preTransparency := .reducible) h2 using 1
  · funext m
    rw [e]
    field_simp
  · field_simp

end GlobalTheory.VolBr
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithHilbertSamuelLogBallCountTendsto =====
