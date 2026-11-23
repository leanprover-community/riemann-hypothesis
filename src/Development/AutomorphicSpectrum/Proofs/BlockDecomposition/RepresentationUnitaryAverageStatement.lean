module

public import Mathlib.Analysis.CStarAlgebra.Module.Constructions
public import Mathlib.MeasureTheory.Group.Measure
public import Mathlib.RepresentationTheory.Basic
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RepresentationUnitaryAverage
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Development.AbelianVarietyTheory.Definitions.Foundations.AestronglyMeasurableQuotMeasureIffLift
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareIntegrableSmoothSubmoduleGL
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeDefiniteUnitary
import Development.AutomorphicArithmetic.IntegralCasts.IsOpenStabOfMemNhds
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.InfinitesimalCharacterLimits.AllLeaves
import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.IsSliceMap

@[expose] public section

open scoped Classical InnerProductSpace ComplexConjugate
open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.Rs PositivityTheory.Rg.BcB.SpectralAccumulation GlobalTheory.AutomorphicL2Unitary GlobalTheory.SqIntGL
open scoped GlobalTheory.CuspRep.CuspidalL2GL

theorem _root_.GlobalTheory.T.representation_unitary_average : ∀ {K M H X : Type} [Group K] [TopologicalSpace K] [IsTopologicalGroup K] [CompactSpace K] [MeasurableSpace K] [BorelSpace K] (ν : Measure K) [ν.IsHaarMeasure] [AddCommGroup M] [Module ℂ M] [NormedAddCommGroup H] [InnerProductSpace ℂ H] (ρ : Representation ℂ K M) (ι : M →ₗ[ℂ] H) (U U' : Submodule ℂ M) (ev : X → M →ₗ[ℂ] ℂ),
  (∀ k, ∀ x ∈ U', ∀ y ∈ U, ⟪ι (ρ k x), ι (ρ k y)⟫_ℂ = ⟪ι x, ι y⟫_ℂ) →
  (∀ k, ∀ x ∈ U', ∀ y ∈ U', ⟪ι (ρ k x), ι (ρ k y)⟫_ℂ = ⟪ι x, ι y⟫_ℂ) →
  (∀ x ∈ U, ∃ A : Submodule ℂ M, FiniteDimensional ℂ A ∧ x ∈ A ∧ A ≤ U ∧ (∀ k, ∀ a ∈ A, ρ k a ∈ A) ∧ ∀ ℓ : M →ₗ[ℂ] ℂ, ∀ a ∈ A, Continuous fun k => ℓ (ρ k a)) →
  (∀ x ∈ U', ∃ A : Submodule ℂ M, FiniteDimensional ℂ A ∧ x ∈ A ∧ A ≤ U' ∧ (∀ k, ∀ a ∈ A, ρ k a ∈ A) ∧ ∀ ℓ : M →ₗ[ℂ] ℂ, ∀ a ∈ A, Continuous fun k => ℓ (ρ k a)) →
  (∀ W : Submodule ℂ (K → ℂ), FiniteDimensional ℂ W → FiniteDimensional ℂ (Submodule.span ℂ {x | x ∈ U' ∧ ∀ t, (fun k => ev t (ρ k x)) ∈ W})) →
  ∀ x ∈ U, ∃ y ∈ U', ∀ z ∈ U', ⟪ι z, ι x⟫_ℂ = ⟪ι z, ι y⟫_ℂ := by
  first | exact @GlobalTheory.CompanionTheory.FinDiscRepr.representing_vector | exact GlobalTheory.CompanionTheory.FinDiscRepr.representing_vector | (intros; apply GlobalTheory.CompanionTheory.FinDiscRepr.representing_vector <;> assumption)
