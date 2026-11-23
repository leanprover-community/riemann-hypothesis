module

public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.IteratedLiftChains
public import Formalism.LocalToGlobal.UnitaryNorms.CharTied
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.NotIsOfFinOrderHeckeCharacterValueCompletelySpli
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions


theorem _root_.GlobalTheory.T.not_isOfFinOrder_heckeCharacter_value_completelySplitPrime : ∀ (D : D7) (χ : Formalism.L2.Host.HChar D.host.E) (a : D.what₂.Tau → ℚ) (p : ℕ), χ.HasInfQ (Formalism.L2.Host.embTau D) a → (∀ τ, a τ ≠ 0) → GlobalTheory.IndefiniteRowSideFullHecke.IteratedLiftChains.SplitsCompletely D p → ∀ w : HeightOneSpectrum (𝓞 D.host.E), (p : 𝓞 D.host.E) ∈ w.asIdeal → ¬ IsOfFinOrder (χ.val w) := by
  first | exact @GlobalTheory.SplitValuePow.not_isOfFinOrder_val | exact GlobalTheory.SplitValuePow.not_isOfFinOrder_val | (intros; apply GlobalTheory.SplitValuePow.not_isOfFinOrder_val <;> assumption)
