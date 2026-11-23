module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormSubLtOneOfFix
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsWittVectorTraceOneFiniteLevel
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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


theorem _root_.GlobalTheory.T.exists_wittVector_trace_one_finiteLevel : ∀ (p : ℕ) [Fact p.Prime] (G : Type) [Group G] (R : Type) [CommRing R] [IsDomain R] [CharP R p] [PerfectRing R p] (ρ : G →* (R ≃+* R)) (m : ℕ), 0 < m → Finite (G ⧸ GlobalTheory.UnramifiedCrys.fixer ρ p m) → ∃ τ : WittVector p R, (∀ g ∈ GlobalTheory.UnramifiedCrys.fixer ρ p m, WittVector.map (ρ g).toRingHom τ = τ) ∧ ∑ᶠ x : G ⧸ GlobalTheory.UnramifiedCrys.fixer ρ p m, WittVector.map (ρ x.out).toRingHom τ = 1 := by
  first | exact @GlobalTheory.UnramifiedCrys.exists_witt_trace_one | exact GlobalTheory.UnramifiedCrys.exists_witt_trace_one | (intros; apply GlobalTheory.UnramifiedCrys.exists_witt_trace_one <;> assumption)
