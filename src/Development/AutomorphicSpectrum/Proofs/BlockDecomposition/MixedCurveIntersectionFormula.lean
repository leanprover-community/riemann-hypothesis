module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsSmoothHermCombLine
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChernPartSingleton
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Topology.Separation.Connected

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi
open GlobalTheory GlobalTheory.ArInt GlobalTheory.Cartier GlobalTheory.CxPts

namespace GlobalTheory.CompanionTheory.MixZ

theorem curveInt : CurveInt := by
  intro Z _ q hq L M r hr
  refine ⟨fun σ => ?_, GlobalTheory.ArchDimZero.main ℤ Z q hq M L r hr⟩
  have := GlobalTheory.ArchDimZero.isProper hq
  have := GlobalTheory.ArchDimZero.finite_cxPts hq σ
  have h₁ : (L.φ σ).chernPart 0 1 = Measure.count := Measure.ext_iff_singleton.2 fun y => by
    rw [GlobalTheory.ArchDimZero.chernPart_singleton hq L σ 1 y, Measure.count_singleton]
    simp
  have h₂ : (L.φ σ).chernPart 0 (-1) = 0 := Measure.ext_iff_singleton.2 fun y => by
    rw [GlobalTheory.ArchDimZero.chernPart_singleton hq L σ (-1) y]
    simp
  refine ⟨?_, ?_⟩
  · rw [h₁]
    exact (Integrable.of_finite (μ := Measure.count) (f := logNorm (M.φ σ) r)).integrableOn
  · rw [h₂]
    exact (integrable_zero_measure : Integrable (logNorm (M.φ σ) r) 0).integrableOn

end GlobalTheory.CompanionTheory.MixZ
