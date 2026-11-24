module

public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.GenericBlockMatrixIsBlockDiag
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.IsFieldIntersection
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagBundlePartialBlockMap
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

open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical

theorem _root_.GlobalTheory.T.flag_bundle_partial_block_map : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n d : ℕ) (Rb : AnLogRes (mCoordIdeal M.x) ⊤ n), d = n + Fintype.card Ψ * (j.choose 2 + (N - j).choose 2) → ∀ (keep : Ψ × Fin N → Prop) (Kk : Type) [Fintype Kk] (ιk : Kk → Type) [∀ k, Fintype (ιk k)] (κ : Kk → K) (v : (Σ k, ιk k) → (Σ k, ι k)), IsBlockMap κ v → (∀ k, k ∈ Set.range κ ↔ ((∀ p, M.blk p ≠ some k) ∨ ∃ p, keep p ∧ M.blk p = some k)) → ∃ (e : ℕ) (R : AnLogRes (mCoordIdeal (y ∘ v)) ⊤ e), ((∀ p, keep p) → e = d) ∧ ∃ pr : R.X → Rb.X, HoloMap R.A Rb.A pr ∧ (∀ x, ∃ z ∈ mcPts (mCoordIdeal y), z ∘ v = R.lift x x ∧ SameOrbit (basePart M.blk z) (Rb.lift (pr x) (pr x))) ∧ ∀ x, ∃ (ψ : OpenPartialHomeomorph R.X (Fin e → ℂ)) (kb : Fin Rb.A.n) (σ : Fin n ↪ Fin e), IsCompatChart R.A ψ ∧ x ∈ ψ.source ∧ (∀ x' ∈ ψ.source, pr x' ∈ (Rb.A.chart kb).source ∧ ∀ i, Rb.A.chart kb (pr x') i = ψ x' (σ i)) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.PFl.main | exact GlobalTheory.CompanionTheory.Ar.PB.PFl.main | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.PFl.main <;> assumption)
