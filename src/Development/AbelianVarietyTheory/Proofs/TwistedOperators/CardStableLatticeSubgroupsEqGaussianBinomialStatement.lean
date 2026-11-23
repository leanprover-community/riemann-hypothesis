module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NonemptyTransferEquiv
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.GaussianBinomialFormula
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CardStableLatticeSubgroupsEqGaussianBinomial
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

@[expose] public section

open NumberField

theorem _root_.GlobalTheory.T.card_stableLatticeSubgroups_eq_gaussianBinomial : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    (Dw : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum H) (p : ℕ) (J : Ideal (𝓞 E)), 0 < p → J.IsMaximal → (p : 𝓞 E) ∈ J → ∀ k : ℕ,
    Nat.card (GlobalTheory.HeckeCount.LatCount Dw p J (Ideal.absNorm J ^ k)) =
      GlobalTheory.IndefiniteRowSideFullHecke.GaussianBinomialFormula.gaussBinom (Ideal.absNorm J) (Module.finrank (𝓞 E) Dw.La) k := by
  first | exact @GlobalTheory.LatCountGauss.card_latCount | exact GlobalTheory.LatCountGauss.card_latCount | (intros; apply GlobalTheory.LatCountGauss.card_latCount <;> assumption)
