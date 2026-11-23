module

public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DisintegrationParameterContinuous
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init
import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FreeCell
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HypOneZeroZero
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsCovolOne
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TrMMemFramesEIff
import Formalism.UnipotentAdelicQuotients.SWXSDefs

@[expose] public section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WeilSiegel.Free GlobalTheory.CompanionTheory.WeilSiegel.HypStep GlobalTheory.CompanionTheory.WeilSiegel.HypStage

theorem _root_.GlobalTheory.T.disintegration_parameter_continuous : ∀ (V H Y P : Type) [TopologicalSpace V] [T2Space V] [LocallyCompactSpace V] [SecondCountableTopology V] [MeasurableSpace V] [BorelSpace V] [TopologicalSpace H] [T2Space H] [LocallyCompactSpace H] [SecondCountableTopology H] [MeasurableSpace H] [BorelSpace H] [TopologicalSpace P] [T2Space P] [LocallyCompactSpace P] (μ : Measure V) (ν : Measure H) (f : V → Y) (ι : H → Y) (q : V → H) (U : Set V) (fam : H → Measure V), IsOpen U → Continuous q → Function.Injective ι → (∀ v, f v = ι (q v)) → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsFibreFamily μ f ι U ν Set.univ fam → ∀ ψ : P × V → ℝ, Continuous ψ → HasCompactSupport ψ → (∀ p ∈ tsupport ψ, p.2 ∈ U) → Continuous (fun z : P × H => ∫ v, ψ (z.1, v) ∂(fam z.2)) ∧ HasCompactSupport (fun z : P × H => ∫ v, ψ (z.1, v) ∂(fam z.2)) ∧ ∀ z ∈ tsupport (fun z : P × H => ∫ v, ψ (z.1, v) ∂(fam z.2)), ∃ v, (z.1, v) ∈ tsupport ψ ∧ q v = z.2 := by
  exact @GlobalTheory.CompanionTheory.WeilSiegel.FibParam.fibre_param_continuous
