module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ScalHHermScal
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SimilitudeScalingHermitianMeasure
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

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

theorem _root_.GlobalTheory.T.similitude_scaling_hermitian_measure : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ l : F, l ≠ 0 → ∃ (cinf : ℝ≥0) (c : HeightOneSpectrum (𝓞 F) → ℝ≥0), IsUnitProd cinf c ∧ (∀ ν : Measure (HermR (Ainf F) σ 1), ν.IsAddHaarMeasure → ν.map (GlobalTheory.CompanionTheory.SW.MassSimil.scalH (Ainf F) σ (algebraMap F (Ainf F) l)) = cinf • ν) ∧ ∀ v : HeightOneSpectrum (𝓞 F), ∀ ν : Measure (HermR (Fv F v) σ 1), ν.IsAddHaarMeasure → ν.map (GlobalTheory.CompanionTheory.SW.MassSimil.scalH (Fv F v) σ (algebraMap F (Fv F v) l)) = c v • ν := by
  first | exact @GlobalTheory.CompanionTheory.SW.MassSimil.ScalModule.scal_module | exact GlobalTheory.CompanionTheory.SW.MassSimil.ScalModule.scal_module | (intros; apply GlobalTheory.CompanionTheory.SW.MassSimil.ScalModule.scal_module <;> assumption)
