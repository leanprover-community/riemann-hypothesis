module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EvalMod
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LubinTateLimitKernelZero
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


theorem _root_.GlobalTheory.T.lubin_tate_limit_kernel_zero : ∀ {B : Type} [CommRing B] {S : Subring B} {F : ℕ → Ideal B} {ϖ : B} {C : Type} [NormedField C], PerEnv S F ϖ → ∀ (ϖ' : B), ϖ * ϖ' = 1 →
    ∀ (θ : B →+* C), (∀ x, θ x = 0 ↔ x ∈ F 1) → (∀ s ∈ S, ‖θ s‖ ≤ 1) → ‖θ ϖ‖ < 1 → ∀ (q : ℕ), 2 ≤ q →
    ∀ Q, θ Q = 0 → ∀ t, Tends S F ϖ (fun n => ϖ' ^ n * ltIter ϖ q n Q) t → θ t = 0 := by
  first | exact @GlobalTheory.CompanionTheory.LTPer.theta_period_eq_zero_of_theta_eq_zero | exact GlobalTheory.CompanionTheory.LTPer.theta_period_eq_zero_of_theta_eq_zero | (intros; apply GlobalTheory.CompanionTheory.LTPer.theta_period_eq_zero_of_theta_eq_zero <;> assumption)
