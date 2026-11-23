module

public import Development.AbelianVarietyTheory.Definitions.Divisors.RangeShape
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DefsRep
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformFinitenessOfReproducingPolynomialAveragin
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


theorem _root_.GlobalTheory.T.uniformFiniteness_of_reproducingPolynomial_averaging : GlobalTheory.PsCo.Pc3.Repro → (∀ (n : ℕ) (ε : Fin n → Bool) (d : ℕ), ∃ A : Set (Fin n → ℝ), A.Finite ∧ ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)), ReciprocityTheory.ChartRestriction.DS.IsURepOn (ReciprocityTheory.ChartRestriction.DS.UJset ε) σ → ∀ u : H, ∃ S : Submodule ℂ H, FiniteDimensional ℂ S ∧ Formalism.MainNotions.S.IsKStableOn ε σ S ∧ (∀ P : GlobalTheory.PsCo.Pc1.Poly n, P.totalDegree ≤ d → ∫ k : Formalism.REAL.KG ε, GlobalTheory.PsCo.Pc1.ev (Formalism.REAL.toMK k) P • σ (Formalism.REAL.toMK k) u ∂(Formalism.REAL.muK ε) ∈ S) ∧ ∀ (μ : Fin n → ℝ) (s : H), s ∈ S → s ≠ 0 → Formalism.MainNotions.S.IsWtOn (Formalism.REAL.Kset ε) σ μ s → μ ∈ A) → GlobalTheory.PsCo.Pc3.UFin := by
  exact GlobalTheory.PsCo.Pc3.uFin_of'
