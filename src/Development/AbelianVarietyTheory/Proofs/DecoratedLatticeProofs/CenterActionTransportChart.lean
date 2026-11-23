module

public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Data.Matrix.Mul
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
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.SphericalZero
import Development.AbelianVarietyTheory.Definitions.Foundations.AestronglyMeasurableQuotMeasureIffLift
import Development.AbelianVarietyTheory.Definitions.Foundations.AnalyticOnNhdTsumNpow
import Development.AbelianVarietyTheory.Definitions.Foundations.EventuallyEqOfIsPreconnected
import Development.AbelianVarietyTheory.Definitions.Foundations.IsIwasawaOfIsCompact
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.HalfData
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.HeckeFormNSOfHeckeForm
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.SphericalEisensteinSeriesOnGroup
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.CovolOneIntegralAdd
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsSmoothAutomorphicFunctionTranslateAtRealPlace
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.RegularisedSiegelWeilFirstTerm
import Formalism.LocalRingCardinality.DataTheta
import Formalism.LocalToGlobal.BesselHermitianTheta.NoncompactGapAtLeastRange
import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
import Formalism.LocalToGlobal.ProjectiveLattices.ErealAddIInf
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes

@[expose] public section

open scoped Matrix NNReal TensorProduct Classical
open MeasureTheory NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.Eis GlobalTheory.MixModel GlobalTheory.RegSW GlobalTheory.RegSch
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (swSec sZero IsKFinVec)
open GlobalTheory.Core.Rk.SW (sch)
open GlobalTheory.Mem.AutSpace (SmFun)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.RegSch.GChart

open GlobalTheory.Mem.AutSpace GlobalTheory.Mem.RealTranslate

variable {D : D7}

theorem trace_pow_conj {R : Type} [Ring R] [Algebra ℂ R] {n : ℕ} (E : Fin n → Fin n → R)
    (P Q : Matrix (Fin n) (Fin n) ℂ) (hQP : Q * P = 1) (m : ℕ) :
    ∑ c, (Matrix.of (fun a b => ∑ c, ∑ d, (P a c * Q d b) • E c d) ^ m) c c = ∑ c, (Matrix.of E ^ m) c c := by
  have hPQ : P * Q = 1 := mul_eq_one_comm.1 hQP
  let φ : Matrix (Fin n) (Fin n) ℂ →+* Matrix (Fin n) (Fin n) R := (algebraMap ℂ R).mapMatrix
  have hc : ∀ (M : Matrix (Fin n) (Fin n) R) a b, (φ P * M * φ Q) a b = ∑ c, ∑ d, (P a c * Q d b) • M c d := by
    intro M a b
    simp only [Matrix.mul_apply, φ, RingHom.mapMatrix_apply, Matrix.map_apply, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => ?_
    rw [← Algebra.smul_def, ← Algebra.commutes, ← Algebra.smul_def, smul_smul, mul_comm]
  have h1 : Matrix.of (fun a b => ∑ c, ∑ d, (P a c * Q d b) • E c d) = φ P * Matrix.of E * φ Q := by
    ext a b
    rw [hc]
    rfl
  have hqp : φ Q * φ P = 1 := by rw [← map_mul, hQP, map_one]
  have h2 : ∀ m : ℕ, (φ P * Matrix.of E * φ Q) ^ m = φ P * Matrix.of E ^ m * φ Q := by
    intro m
    induction m with
    | zero => rw [pow_zero, pow_zero, mul_one, ← map_mul, hPQ, map_one]
    | succ m ih =>
      rw [pow_succ, ih, pow_succ]
      simp only [mul_assoc]
      rw [← mul_assoc (φ Q), hqp, one_mul]
  rw [h1, h2]
  simp only [hc]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [Finset.sum_comm]
  have : ∀ d, ∑ a, (P a c * Q d a) • (Matrix.of E ^ m) c d = (Q * P) d c • (Matrix.of E ^ m) c d := by
    intro d
    rw [← Finset.sum_smul, Matrix.mul_apply]
    simp only [mul_comm]
  simp [this, hQP, Matrix.one_apply]


variable (A : HSp D) (μ : D.host.E) (hμ : GlobalTheory.StdUnn.IsSkew μ) (κ : GA D (dblSp A) ≃* GlobalTheory.StdUnn.G D A.rank)
  (hκ : GlobalTheory.StdUnn.IsChart A μ κ) {θ : InfFam D} (hθ : IsInfFam θ) (τ : D.what₂.Tau)


end GlobalTheory.RegSch.GChart

end
