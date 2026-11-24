module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HermInf
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteAdelicSiegelWeilIntegralIdentity
import Formalism.LocalRingCardinality.DataHost
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
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ModerateGrowthSchwartz
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.WeilSiegelTheta.BigCellDefs

@[expose] public section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC GlobalTheory.CompanionTheory.SiegelND
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.CompanionTheory.SiegelND.Integ


theorem _root_.GlobalTheory.T.finite_adelic_siegel_weil_integral_identity : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
  IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J →
  ∀ n : ℕ, 2 * n < M → ∀ ψ : AddChar (AF F) ℂ, IsCharAF F ψ →
  ∀ μ : Measure (Fin n → Fin M → Af F ⊗[F] E), μ.IsAddHaarMeasure →
  ∀ ν : Measure (HermR (Af F) σ n), ν.IsAddHaarMeasure →
  ∀ Q : (Fin n → Fin M → Af F ⊗[F] E) → ℂ, IsSB Q →
    Integrable (starLoc (Af F) σ J (psiFin F ψ) μ Q) ν := by
  first | exact @GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.integrable_starLoc_fin | exact GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.integrable_starLoc_fin | (intros; apply GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.integrable_starLoc_fin <;> assumption)
