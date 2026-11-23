module

public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DoublingIntegralJointHarmonicPosStatement
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FockSpaceContainsDiscreteSeriesTensorStatement
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FockStructure
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HighestWeightTensor
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LineMatrixKroneckerLeftFactorEqZeroOfIsPC
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LowestTypePositiveAndDecays
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NoIntertwinerSmallerFockToDiscreteSeriesStatement
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PolarCoordinatesUnitaryPQDoubleCoverStatement
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RealPlaceStdParamIsParam
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SymmetrisationInjective
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaCorrespondenceFockDsUniquenessStatement
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible Formalism.L2.Theta

namespace GlobalTheory.RealPlaceTheta

theorem exists_record_theta :
    GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules →
    ∃ X : ProvA, (∀ (p q : ℕ) (lam : Ix p q → ℚ), IsParam lam → HasParam (X.ds p q lam) lam) ∧
      DiscreteSeriesBlattner X ∧ admQ5 X ∧ ArchimedeanRallisFirst X ∧ ArchimedeanRallisSecond X ∧ ArchimedeanRallisUpDownLine X ∧ ArchimedeanRallisFifth X := by
  intro hDS hHC

  obtain ⟨X, hX⟩ := GlobalTheory.exists_provA_of_forall_exists_hasParam fun p q T lam hl =>
    GlobalTheory.CoverDS.exists_hasParam hDS p q T lam hl
  have hH1 : admH1 X := GlobalTheory.FockDeg.degrees_and_adjoints X
  have hH2 : admH2 X := GlobalTheory.FockAlg.fock_structure X
  have hD1 : DiscreteSeriesBlattner X := GlobalTheory.CoverDS.admissibleDiscreteSeries_of_hasParam hDS X hX
  have hQ5 : admQ5 X := GlobalTheory.Published.HarishChandraModules.admQ5_of_harishChandraModules hHC X
  have hQ6 : CoverHaarIntegration X := GlobalTheory.T.polarCoordinates_unitaryPQ_doubleCover X
  have hQ7 : admQ7 := TensorHW.highestWeight_tensor
  have hQ8 : admQ8 := GlobalTheory.InducedPBW.pbw_induced
  have hD2 : DiscreteSeriesPositivity X := GlobalTheory.SphJet.lowest_type_positive_and_decays X hD1 hQ5 hQ7 hQ8
  have hA1 : ArchimedeanRallisFirst X := GlobalTheory.T.doublingIntegral_jointHarmonic_pos X hH1 hH2 hD1 hD2 hQ5 hQ6 hQ7 hQ8
  have hA2 : ArchimedeanRallisSecond X := GlobalTheory.T.fockSpace_contains_discreteSeriesTensor X hH1 hH2 hD1 hD2 hQ5 hQ6 hQ7 hQ8 hA1
  have hA3 : ArchimedeanRallisUpDownLine X := GlobalTheory.T.theta_correspondence_fock_ds_uniqueness X hH1 hH2 hD1 hQ5 hQ7 hQ8 hA1 hA2
  have hA5 : ArchimedeanRallisFifth X := GlobalTheory.T.no_intertwiner_smaller_fock_to_discrete_series X hH1 hH2 hD1 hQ5
  exact ⟨X, hX, hD1, hQ5, hA1, hA2, hA3, hA5⟩

end GlobalTheory.RealPlaceTheta
