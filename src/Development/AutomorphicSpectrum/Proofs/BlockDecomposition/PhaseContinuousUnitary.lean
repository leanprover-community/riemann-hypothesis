module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HermInf
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RatTuple
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.FiniteAdeleTopologyStatement
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.TensorLocallyCompactRingStatement
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
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ModerateGrowthSchwartz
import Development.AbelianVarietyTheory.Definitions.Foundations.AestronglyMeasurableQuotMeasureIffLift
import Development.AbelianVarietyTheory.Definitions.Foundations.EventuallyEqOfIsPreconnected
import Development.AbelianVarietyTheory.Definitions.Foundations.IsIwasawaOfIsCompact
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.CovolOneIntegralAdd
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitarySchrodinger
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HermOf
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ThetaPartD
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.WeilSiegelTheta.BigCellDefs
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.WeilSiegelTheta.ThetaOrbits
import Formalism.LocalRingCardinality.DataTheta
import Formalism.LocalToGlobal.BesselHermitianTheta.NoncompactGapAtLeastRange
import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
import Formalism.LocalToGlobal.ProjectiveLattices.ErealAddIInf

@[expose] public section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC GlobalTheory.CompanionTheory.SiegelND
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.CompanionTheory.SiegelND.Integ GlobalTheory.CompanionTheory.SiegelND.Integ.Hua
open NumberField
open GlobalTheory.CompanionTheory.SiegelND.Integ.Weyl GlobalTheory.CompanionTheory.SW.Core

namespace GlobalTheory.CompanionTheory.SiegelND.Integ.Weyl

theorem psiFin_continuous_unit (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ)
    (hψ : IsCharAF F ψ) : Continuous (psiFin F ψ) ∧ ∀ y, ‖psiFin F ψ y‖ = 1 := by
  refine ⟨?_, fun y => hψ.2.1 _⟩
  have : Continuous fun y : Af F => pairA F 0 y := continuous_const.prodMk continuous_id
  exact hψ.1.comp this



theorem phaseB_pairB_props : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E)
    (n : ℕ) (ψ : AddChar (AF F) ℂ), IsCharAF F ψ → ∀ (b : HermR (Af F) σ n),
    Continuous (phaseB σ J (psiFin F ψ) b) ∧ (∀ X, ‖phaseB σ J (psiFin F ψ) b X‖ = 1) ∧
    ∀ X, Continuous (pairB σ J (psiFin F ψ) b X) := by
  intro F E _ _ _ _ _ σ hσ M J n ψ hψ b
  obtain ⟨a1, a2, a3, -, -, -, -, -, -, -⟩ := GlobalTheory.T.mem_Oh_iff_and_nat_mul_properties F
  haveI : LocallyCompactSpace (Af F) := a1
  haveI : SecondCountableTopology (Af F) := a2
  haveI : T2Space (Af F) := a3
  obtain ⟨t1, -, -, -, hs, htr, -, -, -, hG⟩ := GlobalTheory.T.tensor_locally_compact_ring F E σ hσ (Af F)
  haveI : IsTopologicalRing (Af F ⊗[F] E) := t1
  obtain ⟨hc, hn⟩ := psiFin_continuous_unit F ψ hψ
  refine ⟨?_, fun X => hn _, fun X => ?_⟩
  · refine hc.comp (continuous_const.mul (htr.comp (Continuous.matrix_trace
      (Continuous.matrix_mul continuous_const (hG n M J)))))
  · refine hc.comp (htr.comp (Continuous.matrix_trace
      (Continuous.matrix_mul continuous_const ?_)))
    refine continuous_matrix fun a c => ?_
    simp only [gram2, hR, Formalism.UG.hform]
    refine continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ => ?_
    exact continuous_const.mul ((continuous_apply j).comp (continuous_apply c))

end GlobalTheory.CompanionTheory.SiegelND.Integ.Weyl
