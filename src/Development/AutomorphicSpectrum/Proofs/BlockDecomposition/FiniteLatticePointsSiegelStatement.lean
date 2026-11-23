module

public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeDefiniteUnitary
public import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.ExponentialNegativity.L2DecayOfCountEscape
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteLatticePointsSiegel
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
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UfamConst

@[expose] public section

open scoped ENNReal
open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology Polynomial
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.Rs GlobalTheory.CompanionTheory.Conc
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.AutomorphicForm

theorem _root_.GlobalTheory.T.finite_lattice_points_siegel : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (N : ℕ), ∃ M : ℝ, 0 ≤ M ∧ ∀ (Q' : Set (GA E N)) (ω : Set (GA E N)) (t₀ : ℝ)
  (Q : Set (GA E N)), IsCompact Q' → IsCompact ω → ω ⊆ (adelicBorel (K := E) (n := N) : Set _) → IsCompact Q → ∃ C : ℝ, ∀ b ∈ ω, ∀ x : Fin N → ℝ,
    (∀ r, -t₀ ≤ An.sr x r) → ∀ q ∈ Q,
    {γ : GA E N | γ ∈ latticeGL E N ∧ ∃ a ∈ Q', ∃ a' ∈ Q', γ = (b * An.tor E x * q) * a * a'⁻¹ * (b * An.tor E x * q)⁻¹}.encard ≤
      (⌈C * Real.exp (M * ∑ r ∈ Finset.range N, An.sr x r)⌉₊ : ℕ) := by
  first | exact @GlobalTheory.CompanionTheory.ConcCount.count_conj_siegel | exact GlobalTheory.CompanionTheory.ConcCount.count_conj_siegel | (intros; apply GlobalTheory.CompanionTheory.ConcCount.count_conj_siegel <;> assumption)
