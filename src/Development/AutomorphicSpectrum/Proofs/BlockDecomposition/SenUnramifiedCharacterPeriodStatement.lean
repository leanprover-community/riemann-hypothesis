module

public import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
public import GroundTheory.PAdicHodge.LocalBridge
public import GroundTheory.PAdicHodge.NormalizedTraceTower
public import GroundTheory.PAdicHodge.SenTateCharTower
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SenUnramifiedCharacterPeriod
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
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LocalPrimeGaloisActionPeriodT
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TripleAtt
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EvalMod
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HasPeriods
import Formalism.ConjugateSelfDual.Statement
import Formalism.LocalToGlobal.UnitaryNorms.IsUnitaryNormOf
import ReciprocityTheory.GaloisValuations.GlobalA
import ReciprocityTheory.NeutralLocalFields.Reciprocity

@[expose] public section

noncomputable section
open NumberField IsDedekindDomain Neutral.B1 Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations
open GlobalTheory.HeckeGal GlobalTheory.Pst GlobalTheory.TripleGal GlobalTheory.CompanionTheory.LTHodge GlobalTheory.CompanionTheory.LTPer
open scoped Classical


theorem _root_.GlobalTheory.T.sen_unramified_character_period : ∀ {l : ℕ} [Fact l.Prime], ∀ (E : IntermediateField ℚ_[l] (Om l)) [FiniteDimensional ℚ_[l] ↥E] (ψ : Gal(Om l/↥E) →* ℤ_[l]ˣ), Continuous ψ →
      (∀ σ, GroundTheory.LocalField.unramifiedDegree ↥E (Om l) σ = 1 → ψ σ = 1) →
      ∃ f : ℕ, 0 < f ∧ ∃ x : ℂ_[l], x ≠ 0 ∧ ∀ σ : Gal(Om l/↥E),
        σ • x = algebraMap ℚ_[l] ℂ_[l] ((((ψ σ : ℤ_[l]ˣ) : ℤ_[l]) : ℚ_[l]) ^ f) * x := by
  first | exact @GlobalTheory.CompanionTheory.LTPer.exists_pow_eigenvector_of_unramified_units | exact GlobalTheory.CompanionTheory.LTPer.exists_pow_eigenvector_of_unramified_units | (intros; apply GlobalTheory.CompanionTheory.LTPer.exists_pow_eigenvector_of_unramified_units <;> assumption)
