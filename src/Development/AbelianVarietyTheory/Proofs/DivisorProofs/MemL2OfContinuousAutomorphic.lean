module

public import Development.AbelianVarietyTheory.Definitions.Foundations.AestronglyMeasurableQuotMeasureIffLift
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ClassFunctionSumIntegral
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.IntegrableOnFundamentalDomainOfCocompact
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdelicUnitaryTopology
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsBoundedUnitary
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MeasureFundamentalDomainLtTop
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
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VacTheta

@[expose] public section

open NumberField MeasureTheory
open scoped Classical
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum
open GlobalTheory.NormSum (Pair Tup minorPol ratG intG Cls gam)
open GlobalTheory.NormDict

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.DefiniteSqInt

theorem memL2_of_continuous_definite : ∀ {D : D7} (V : HSp D) (K : Subgroup (GL (Fin V.rank) (Lev.EAf D))) (μ : Measure (GA D V)) (𝓕 : Set (GA D V)),
    GlobalTheory.IndefiniteRowSideFullHecke.ClassFunctionSumIntegral.IsDefiniteSpace V → GlobalTheory.IndefiniteRowSideFullHecke.ClassFunctionSumIntegral.IsOpenCompactLevel V K → Links.IsMeasDef V K μ 𝓕 →
    ∀ u : GA D V → ℂ, Continuous u → (∀ γ ∈ GQ V, ∀ h, u (γ * h) = u h) → GlobalTheory.AutomorphicL2Unitary.MemL2Quotient (GQ V) μ u := by
  intro D V K μ 𝓕 hV _ hμ u hu hinv
  have hT := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D V
  haveI := hT.2.2.2.2.2.2
  have := hμ.1.1
  obtain ⟨C, hC, hcov⟩ := GlobalTheory.Mem.AnisoQuotient.exists_compact D V
    (GlobalTheory.BesselConvDefinite.isAniso_of_isDefinite V hV.1 hV.2)
  have hcov' : ∀ g : GA D V, ∃ γ ∈ GQ V, γ * g ∈ C := fun g => by
    obtain ⟨γ, hγ, c, hc, rfl⟩ := hcov g
    exact ⟨γ⁻¹, inv_mem hγ, by rwa [inv_mul_cancel_left]⟩
  refine (GlobalTheory.AutomorphicL2Unitary.memL2_iff_fundamental_domain hμ.2).2 ⟨hinv, (memLp_two_iff_integrable_sq_norm hu.aestronglyMeasurable).2 ?_⟩
  simpa only [← _root_.norm_pow] using (GlobalTheory.integrableOn_fundamentalDomain_of_cocompact _ (GQ V) C hC hcov' μ
    inferInstance 𝓕 hμ.2 (fun g => u g ^ 2) (hu.pow 2) fun γ hγ g => by rw [hinv γ hγ]).norm

end GlobalTheory.DefiniteSqInt
