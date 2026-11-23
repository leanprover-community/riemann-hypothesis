module

public import GroundTheory.AutomorphicForms.InductionParabolic
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AdmissibleCentralLeviFixedSubmodule
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
import Development.AbelianVarietyTheory.Definitions.Foundations.MatrixMeasurableSpace
import Development.AbelianVarietyTheory.Definitions.Foundations.SmoothPartStable
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivOfRangeEq
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.LeviEmbMemNormalizerLower

@[expose] public section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult

theorem _root_.GlobalTheory.T.admissible_central_levi_fixed_submodule : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], ∀ (N : ℕ) {V : Type} [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V), GroundTheory.Automorphic.IsAdmissible π → ∀ {h : ℕ} (β : Fin N → Fin h), Monotone β → ∀ (a : GL (Fin N) k) (ha : a ∈ GroundTheory.Automorphic.Parabolic.levi k N β), (∀ y ∈ GroundTheory.Automorphic.Parabolic.levi k N β, a * y = y * a) → ∀ (W T : Submodule ℂ (GroundTheory.Automorphic.Parabolic.JacquetModule k N β π)) (Λ : ℂ), Λ ≠ 0 → T ≤ W → (∀ w ∈ W, GroundTheory.Automorphic.Parabolic.jacquetAction k N β π ⟨a, ha⟩ w ∈ W) → (∀ w ∈ W, GroundTheory.Automorphic.Parabolic.jacquetAction k N β π ⟨a, ha⟩ w - Λ • w ∈ T) → (∃ w ∈ W, w ∉ T) → ∃ m₀ : ℕ, ∀ m : ℕ, m₀ ≤ m → ∃ y : GroundTheory.Automorphic.Parabolic.JacquetModule k N β π, y ≠ 0 ∧ (∀ g : GroundTheory.Automorphic.Parabolic.levi k N β, (g : GL (Fin N) k) ∈ GroundTheory.Automorphic.GLnLocal.congruenceSubgroup k N m → GroundTheory.Automorphic.Parabolic.jacquetAction k N β π g y = y) ∧ GroundTheory.Automorphic.Parabolic.jacquetAction k N β π ⟨a, ha⟩ y = Λ • y := by
  first | exact @GlobalTheory.CompanionTheory.JacquetEigen.exists_eigenvector_fixed | exact GlobalTheory.CompanionTheory.JacquetEigen.exists_eigenvector_fixed | (intros; apply GlobalTheory.CompanionTheory.JacquetEigen.exists_eigenvector_fixed <;> assumption)
