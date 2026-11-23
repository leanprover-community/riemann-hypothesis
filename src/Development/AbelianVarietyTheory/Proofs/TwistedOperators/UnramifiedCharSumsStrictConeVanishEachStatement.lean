module

public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ExponentSeparation
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnramifiedCharSumsStrictConeVanishEach
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

@[expose] public section

open GlobalTheory GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL ValuativeRel

theorem _root_.GlobalTheory.T.unramified_char_sums_strict_cone_vanish_each : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ϖ : kˣ), valuation k (ϖ : k) = uniformizer k → ∀ (r n : ℕ) (E : Fin n → Multiset ((Fin r → kˣ) →* ℂˣ)) (c : Fin n → ℂ), (∀ i, ∀ χ ∈ E i, ∀ t ∈ torusO k (Fin r), χ t = 1) → (∀ t ∈ IndefiniteRowSideFullHecke.ExponentSeparationTwistedDiscreteSeries.strictCone ϖ r, ∑ i, c i * IndefiniteRowSideFullHecke.ExponentSeparationTwistedDiscreteSeries.charSum (E i) t = 0) → ∀ [DecidableEq ((Fin r → kˣ) →* ℂˣ)] (χ : (Fin r → kˣ) →* ℂˣ), ∑ i, c i * ((E i).count χ : ℂ) = 0 := by
  first | exact @GlobalTheory.ConeCount.sum_count_eq_zero | exact GlobalTheory.ConeCount.sum_count_eq_zero | (intros; apply GlobalTheory.ConeCount.sum_count_eq_zero <;> assumption)
