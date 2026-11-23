module

public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ClassFunctionSumIntegral
public import Development.AbelianVarietyTheory.Definitions.Foundations.AestronglyMeasurableQuotMeasureIffLift
public import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralDefiniteUnitaryQuotientEqClassSum
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VacTheta

@[expose] public section

open NumberField MeasureTheory
open scoped Classical
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum
open GlobalTheory.NormSum (Pair Tup minorPol ratG intG Cls gam)
open GlobalTheory.NormDict

attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.integral_definiteUnitaryQuotient_eq_classSum : ∀ {D : D7} (V : HSp D) (n : ℕ) (ι : Formalism.MainNotions.StandardLatticesGL3.GA D n →* GA D V) (J : Subgroup (Formalism.MainNotions.StandardLatticesGL3.GA D n))
  (K : Subgroup (GL (Fin V.rank) (Lev.EAf D))) (μ : Measure (GA D V)) (𝓕 : Set (GA D V)),
  GlobalTheory.IndefiniteRowSideFullHecke.ClassFunctionSumIntegral.IsDefiniteSpace V → Function.Injective ι → ι.range = GfC V →
  (∀ x, (∃ γ ∈ GQ V, finHom V γ = finHom V (ι x)) ↔ x ∈ ratG D n) →
  GlobalTheory.IndefiniteRowSideFullHecke.ClassFunctionSumIntegral.IsOpenCompactLevel V K → (∀ x, Lev.finE V (ι x) ∈ K ↔ x ∈ J) → Links.IsMeasDef V K μ 𝓕 →
  ∀ Φ : GA D V → ℂ, GlobalTheory.IndefiniteRowSideFullHecke.ClassFunctionSumIntegral.IsClassFun V K Φ →
    Finite (Cls D n J) ∧ Integrable (GlobalTheory.AutomorphicL2Unitary.descend (GQ V) Φ) (GlobalTheory.AutomorphicL2Unitary.autMeasure V μ) ∧
    ∫ q, GlobalTheory.AutomorphicL2Unitary.descend (GQ V) Φ q ∂GlobalTheory.AutomorphicL2Unitary.autMeasure V μ =
      ∑ᶠ x : Cls D n J, ((gam D J x.out : ℂ))⁻¹ * Φ (ι x.out) := by
  first | exact @GlobalTheory.NormDictClassSum.integral_eq_classSum | exact GlobalTheory.NormDictClassSum.integral_eq_classSum | (intros; apply GlobalTheory.NormDictClassSum.integral_eq_classSum <;> assumption)
