module

public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsUnitarisableOfCharIff
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiltrationUniqueSubquotient
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open GlobalTheory.PRep GlobalTheory.SmGL
open scoped TensorProduct

theorem _root_.GlobalTheory.T.filtration_unique_subquotient : ∀ {G V W : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] (π : Representation ℂ G V) (σ : Representation ℂ G W) (N : ℕ) (S : Fin (N + 1) → Subrepresentation π), Monotone S → S 0 = ⊥ → S (Fin.last N) = ⊤ → ∀ t₀ : Fin N, (∀ φ ψ : (subQuot (S t₀.succ) (S t₀.castSucc)).IntertwiningMap σ, φ.toLinearMap = 0 ∨ ∃ c : ℂ, ψ.toLinearMap = c • φ.toLinearMap) → (∀ t : Fin N, t ≠ t₀ → ∀ φ : (subQuot (S t.succ) (S t.castSucc)).IntertwiningMap σ, φ.toLinearMap = 0) → ∀ φ ψ : π.IntertwiningMap σ, φ.toLinearMap = 0 ∨ ∃ c : ℂ, ψ.toLinearMap = c • φ.toLinearMap := by
  first | exact @GlobalTheory.CompanionTheory.Filtration.intertwining_proportional | exact GlobalTheory.CompanionTheory.Filtration.intertwining_proportional | (intros; apply GlobalTheory.CompanionTheory.Filtration.intertwining_proportional <;> assumption)
