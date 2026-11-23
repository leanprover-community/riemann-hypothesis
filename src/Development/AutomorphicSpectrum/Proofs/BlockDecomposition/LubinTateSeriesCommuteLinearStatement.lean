module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EvalMod
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LubinTateSeriesCommuteLinear
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


theorem _root_.GlobalTheory.T.lubin_tate_series_commute_linear : ∀ {B : Type} [CommRing B] {S : Subring B} {F : ℕ → Ideal B} {ϖ : B} {R : Type} [CommRing R], PerEnv S F ϖ → ∀ (ϖ' : B), ϖ * ϖ' = 1 →
    ∀ (h : R →+* B), (∀ c, h c ∈ S) → ∀ (π : R), h π = ϖ → ∀ (q : ℕ), 2 ≤ q → (∃ s ∈ S, (q : B) = ϖ * s) →
    ∀ (φ : PowerSeries R), PowerSeries.constantCoeff φ = 0 →
      PowerSeries.subst φ (PowerSeries.C π * PowerSeries.X + PowerSeries.X ^ q : PowerSeries R) = PowerSeries.subst (PowerSeries.C π * PowerSeries.X + PowerSeries.X ^ q : PowerSeries R) φ →
    ∀ (σ : B →+* B), (∀ s ∈ S, σ s ∈ S) → (∀ k, ∀ x ∈ F k, σ x ∈ F k) → σ ϖ = ϖ →
    ∀ Q ∈ S, (∃ M : ℕ, 0 < M ∧ Near S ϖ (F 1) 1 (Q ^ M)) →
      (∀ m, EvalMod S F ϖ h φ Q (σ Q) m) →
    ∀ t, Tends S F ϖ (fun n => ϖ' ^ n * ltIter ϖ q n Q) t → σ t = h (PowerSeries.coeff 1 φ) * t := by
  first | exact @GlobalTheory.CompanionTheory.LTPer.galois_log | exact GlobalTheory.CompanionTheory.LTPer.galois_log | (intros; apply GlobalTheory.CompanionTheory.LTPer.galois_log <;> assumption)
