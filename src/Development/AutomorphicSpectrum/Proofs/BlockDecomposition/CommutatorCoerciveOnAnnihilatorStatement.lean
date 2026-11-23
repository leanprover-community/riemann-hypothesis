module

public import Formalism.RealPlaceAnalysis.Complexify
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CommutatorCoerciveOnAnnihilator
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
import Development.WeilBound.RepresentationTheoryGL.HolomorphicDiscreteSeries.EmbeddedFrames.PfD

@[expose] public section

open Finset Matrix PositivityTheory.RgHe.Frame

theorem _root_.GlobalTheory.T.commutator_coercive_on_annihilator : ∀ {m : ℕ} (X : Matrix (Fin m) (Fin m) ℂ) (v : Fin m → ℂ), (∀ A : Matrix (Fin m) (Fin m) ℂ, A * X = X * A → A *ᵥ v = 0 → A = 0) → ∃ c : ℝ, 0 < c ∧ ∀ A : Matrix (Fin m) (Fin m) ℂ, A *ᵥ v = 0 → Formalism.REAL.hs A ≤ c * Formalism.REAL.hs (A * X - X * A) := by
  first | exact @GlobalTheory.CompanionTheory.RgHeFrame.hs_le_commutator | exact GlobalTheory.CompanionTheory.RgHeFrame.hs_le_commutator | (intros; apply GlobalTheory.CompanionTheory.RgHeFrame.hs_le_commutator <;> assumption)
