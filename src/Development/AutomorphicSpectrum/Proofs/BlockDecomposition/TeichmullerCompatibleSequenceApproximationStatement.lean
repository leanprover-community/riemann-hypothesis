module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NormSubLeOfNear
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TeichmullerCompatibleSequenceApproximation
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LocalPrimeGaloisActionPeriodT
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TripleAtt
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Formalism.LocalToGlobal.UnitaryNorms.IsUnitaryNormOf
import ReciprocityTheory.NeutralLocalFields.Reciprocity

@[expose] public section

noncomputable section
open NumberField IsDedekindDomain Neutral.B1 Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations
open GlobalTheory.HeckeGal GlobalTheory.Pst GlobalTheory.TripleGal GlobalTheory.CompanionTheory.LTHodge GlobalTheory.CompanionTheory.LTPer
open scoped Classical
open GlobalTheory.CompanionTheory.LTPer.Tilt

theorem _root_.GlobalTheory.T.teichmuller_compatible_sequence_approximation : ∀ {l : ℕ} [Fact l.Prime] (f : ℕ) (ρ : ℝ), 0 < f → ‖(l : ℂ_[l])‖ ≤ ρ → ρ < 1 → ∀ Z : ℕ → ℂ_[l],
    (∀ n, ‖Z n‖ ≤ 1) → (∀ n, ‖Z (n + 1) ^ l ^ f - Z n‖ ≤ ρ) →
    ∃ u : ℕ → Tl l, (∀ n, u (n + 1) ^ l ^ f = u n) ∧ ∀ n, ‖sh (u n) - Z n‖ ≤ ρ := by
  first | exact @GlobalTheory.CompanionTheory.LTPer.Tilt.exists_tilt_lift_compat | exact GlobalTheory.CompanionTheory.LTPer.Tilt.exists_tilt_lift_compat | (intros; apply GlobalTheory.CompanionTheory.LTPer.Tilt.exists_tilt_lift_compat <;> assumption)
