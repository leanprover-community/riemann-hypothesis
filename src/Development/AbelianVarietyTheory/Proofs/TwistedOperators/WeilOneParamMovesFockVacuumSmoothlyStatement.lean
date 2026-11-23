module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PairInfApply
public import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
public import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilOneParamMovesFockVacuumSmoothly
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.MatchingAdjoints
import Development.AbelianVarietyTheory.Definitions.Foundations.IsIwasawaOfIsCompact
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.HermitianOrthogonalExtensionData
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsVacFOfIsVacVec
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BlkGLMem
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaEqB
import Formalism.LocalRingCardinality.DataTheta
import Formalism.LocalToGlobal.BesselHermitianTheta.NoncompactGapAtLeastRange
import Formalism.LocalToGlobal.Divisibility.CoefMod
import Formalism.LocalToGlobal.IndefiniteForms.IndefSide
import Formalism.LocalToGlobal.IndefiniteReal.IndefiniteWeightData
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GapAtLeast
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped Classical

theorem _root_.GlobalTheory.T.weilOneParam_moves_fockVacuum_smoothly : ∀ {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
    (μ : Measure V) [μ.IsAddHaarMeasure] (β : V →ₗ[ℝ] V →ₗ[ℝ] ℝ), (∀ q, (∀ x, β x q = 0) → q = 0) →
    ∀ T : ℝ → SchwartzMap V ℂ →ₗ[ℂ] SchwartzMap V ℂ, (∀ s t f, T (s + t) f = T s (T t f)) → (∀ f, T 0 f = f) →
    (∀ t f, ∫ x, ‖T t f x‖ ^ 2 ∂μ = ∫ x, ‖f x‖ ^ 2 ∂μ) →
    ∀ A : ℝ → (V × V) →ₗ[ℝ] (V × V), (∀ w, Continuous fun t => A t w) → (∀ s t, A (s + t) = (A s).comp (A t)) →
    A 0 = LinearMap.id →
    (∀ (t : ℝ) (p q : V) (f g : SchwartzMap V ℂ), ⇑g = GlobalTheory.GaussLine.heisFun β p q ⇑f →
      ⇑(T t g) = GlobalTheory.GaussLine.heisFun β (A t (p, q)).1 (A t (p, q)).2 ⇑(T t f)) →
    (∀ f x, Continuous fun t => T t f x) →
    ∀ J₀ : (V × V) →ₗ[ℝ] (V × V), (∀ w, J₀ (J₀ w) = -w) →
    ∀ f₀ : SchwartzMap V ℂ, (∀ w x, GlobalTheory.GaussLine.dHeis β (J₀ w) ⇑f₀ x = Complex.I * GlobalTheory.GaussLine.dHeis β w ⇑f₀ x) →
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun p : ℝ × V => T p.1 f₀ p.2) ∧
    ∃ (n : ℕ) (qs qs' : Fin n → V) (cs : Fin n → ℂ) (c : ℂ), ∀ x,
      HasDerivAt (fun t => T t f₀ x) (∑ i, cs i * (β x (qs i) : ℂ) * (β x (qs' i) : ℂ) * f₀ x + c * f₀ x) 0 := by
  first | exact @GlobalTheory.WeilVacuum.smooth_flow | exact GlobalTheory.WeilVacuum.smooth_flow | (intros; apply GlobalTheory.WeilVacuum.smooth_flow <;> assumption)
