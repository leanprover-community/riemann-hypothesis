module

public import Development.AbelianVarietyTheory.Definitions.Divisors.TupleReadBaseTupleEqFamily
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RunSizesQuotientGapsLarge
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Development.AbelianVarietyTheory.Definitions.Divisors.AevalEqZeroOfMemConeIdeal
import Development.AbelianVarietyTheory.Definitions.Divisors.NormNegCmConstantEqAtAllEmbeddings
import Development.AbelianVarietyTheory.Definitions.Foundations.IsProbabilityMeasureMuPart
import Development.AbelianVarietyTheory.Definitions.Divisors.CuspIso
import Development.AbelianVarietyTheory.Definitions.Divisors.IsoOverOfIsOpenImmersion

@[expose] public section

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.BigTop GlobalTheory.CovTop
  GlobalTheory.CompHS GlobalTheory.HSApp


theorem _root_.GlobalTheory.T.runSizes_quotientGaps_large : Closed FamHyp fun Fm _ => ∃ x0 : ℝ, ∀ (x : ℝ) (hx : Fm.x1 < x), x0 ≤ x → ∀ ι : Fm.Ix x,
    1 ≤ (Fm.D x ι).R.f * (Fm.D x ι).R.r.choose 2 ∧
    (Fm.D x ι).R.f * (Fm.D x ι).R.r.choose 2 + 1 ≤
      ⌈(Fm.parT x hx ι).PP ^ 2 * (((Fm.D x ι).R.f * (Fm.D x ι).R.r.choose 2 : ℕ) : ℝ) ^ 2 * ((Fm.D x ι).R.k : ℝ) /
        ((Fm.D x ι).R.m : ℝ)⌉₊ ∧
    ∀ G T : ℕ, G = ((Fm.D x ι).R.f * (Fm.D x ι).R.r.choose 2 + 3) *
        (((Fm.D x ι).R.f * (Fm.D x ι).R.r.choose 2 + 1).choose 2 + 4 * (Fm.D x ι).R.r +
          (Fm.D x ι).R.f * (Fm.D x ι).R.r.choose 2 + 3) →
      T = ⌈(Fm.parT x hx ι).PP ^ 2 * (((Fm.D x ι).R.f * (Fm.D x ι).R.r.choose 2 : ℕ) : ℝ) ^ 2 * ((Fm.D x ι).R.k : ℝ) /
        ((Fm.D x ι).R.m : ℝ)⌉₊ →
      ((G * (T + (Fm.D x ι).R.f * (Fm.D x ι).R.r.choose 2 + 1) : ℕ) : ℝ) + 4 ≤
          min (LevelStarExponents.gapS (Fm.D x ι) (Fm.params x hx ι).Cgap) (LevelStarExponents.h0 (Fm.L x ι)) ∧
        ((G * (T + (Fm.D x ι).R.f * (Fm.D x ι).R.r.choose 2 + 1) : ℕ) : ℝ) + 22 * ((Fm.D x ι).R.f : ℝ) ^ 2 * ((Fm.D x ι).R.r : ℝ) ^ 4 +
          2 * (Fm.D x ι).R.r + 1 ≤ LevelStarExponents.h0 (Fm.L x ι) := by
  exact @GlobalTheory.RunSizes.gaps_large
