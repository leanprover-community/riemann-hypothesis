module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BorelParam
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SupportParahoricBiTransformingDoubleCosets
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasBoundedSumsOne

@[expose] public section

open MeasureTheory ValuativeRel Matrix GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.Doubling GlobalTheory.GLDoubling GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection GlobalTheory.ZonalCellDecomposition GlobalTheory.SatakeBound

theorem _root_.GlobalTheory.T.support_parahoricBiTransforming_doubleCosets : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ϖ : kˣ), valuation k (ϖ : k) = uniformizer k →
  ∀ (r l t : ℕ) (ξ : kˣ →* ℂˣ), IsTame ξ → ¬ IsUnram ξ →
  ∀ φ : GL (Fin r ⊕ Blocks l t) k → ℂ, IsBiType ξ φ →
    (∀ x y, φ (emb₂ k (Equiv.refl (Fin r ⊕ Blocks l t)) (x, y)) ≠ 0 → x ∈ KO k (Fin r)) →
    ∀ g, φ g ≠ 0 → ∃ e : Fin (l * t) → ℤ, Antitone e ∧ g ∈ dcell ϖ (e ∘ (blkEquiv l t).symm) := by
  first | exact @GlobalTheory.ChainStepSupp.support_dcell | exact GlobalTheory.ChainStepSupp.support_dcell | (intros; apply GlobalTheory.ChainStepSupp.support_dcell <;> assumption)
