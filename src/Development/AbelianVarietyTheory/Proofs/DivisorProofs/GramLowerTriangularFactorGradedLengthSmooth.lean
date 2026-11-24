module

public import Development.AbelianVarietyTheory.Definitions.Divisors.IsMetricFrOfIsMetricOn
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

@[expose] public section

open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc
open scoped Matrix ContDiff ComplexOrder

namespace GlobalTheory.ChernCalc

theorem leadMinor_re_pos_of_posDef {s : ℕ} {G : Matrix (Fin s) (Fin s) ℂ} (hG : G.PosDef) (j : ℕ) :
    0 < (leadMinor G j).re := by
  have hsub : (G.submatrix (Subtype.val : {a : Fin s // (a : ℕ) < j} → Fin s) Subtype.val).PosDef :=
    hG.submatrix Subtype.val_injective
  have h := hsub.det_pos
  unfold leadMinor
  exact (Complex.pos_iff.mp h).1

theorem contDiffAt_leadMinor {n s : ℕ} {G : V n → Matrix (Fin s) (Fin s) ℂ} {v : V n}
    (h : MContDiffAt ∞ G v) (j : ℕ) : ContDiffAt ℝ ∞ (fun x => leadMinor (G x) j) v :=
  (h.submatrix _ _).det

theorem ldPart_grD_smooth : ∀ (n s : ℕ) (G : V n → Matrix (Fin s) (Fin s) ℂ) (v : V n), MContDiffAt ∞ G v → (G v).PosDef →
    MContDiffAt ∞ (fun x => ldPart (G x)) v ∧ ∀ i, ContDiffAt ℝ ∞ (fun x => grD (G x) i) v := by
  intro n s G v hG hp
  refine ⟨fun i j => ?_, fun i => ?_⟩
  · have hnum : ContDiffAt ℝ ∞ (fun x => ((G x).submatrix
        (fun a : {a : Fin s // (a : ℕ) < j + 1} => if a.1 = j then i else a.1) Subtype.val).det) v :=
      (hG.submatrix _ _).det
    have hden := contDiffAt_leadMinor hG (j : ℕ)
    have hne : leadMinor (G v) j ≠ 0 := fun h0 => by
      have := leadMinor_re_pos_of_posDef hp j
      rw [h0] at this; simp at this
    simp only [ldPart, Matrix.of_apply]
    exact hnum.mul (hden.inv hne)
  · have hnum : ContDiffAt ℝ ∞ (fun x => (leadMinor (G x) (i + 1)).re) v :=
      Complex.reCLM.contDiff.contDiffAt.comp v (contDiffAt_leadMinor hG _)
    have hden : ContDiffAt ℝ ∞ (fun x => (leadMinor (G x) i).re) v :=
      Complex.reCLM.contDiff.contDiffAt.comp v (contDiffAt_leadMinor hG _)
    exact hnum.div hden (leadMinor_re_pos_of_posDef hp i).ne'

end GlobalTheory.ChernCalc
