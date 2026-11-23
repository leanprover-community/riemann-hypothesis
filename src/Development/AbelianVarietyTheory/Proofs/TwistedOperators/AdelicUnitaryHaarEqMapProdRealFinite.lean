module

public import Formalism.LocalToGlobal.BesselHermitianTheta.IsAutFunDef
import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsUniqueIsProdMeasureFinAway
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnitaryAdelicInfFinSplitPeriodsUnimodular
import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.IdemElt
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicLocalCompactness.T2SpaceTensorProductFiniteExtension
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.TopoAF
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.LevelPlusSubgroup
import Development.AbelianVarietyTheory.Definitions.Divisors.CmHostImaginaryGeneratorNeZero
import Development.AbelianVarietyTheory.Definitions.Divisors.NatCastSmulMemHatL
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.DepthPays
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsHeightLeTwoMulQuotHeight
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsVacFOfIsVacVec
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.OffQOfSizeRows
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.ChainFr GlobalTheory.SepRows GlobalTheory.SepPer Matrix
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.HaarSplit
open scoped ENNReal NNReal

theorem haar_eq_map_prod : ∀ (D : D7) (Y : HSp D) (ν : Measure (GA D Y)), ν.IsHaarMeasure → ∃ (m : Measure (GinfC Y)) (μ : Measure (GfC Y)), m.IsHaarMeasure ∧ μ.IsHaarMeasure ∧ SigmaFinite m ∧ SigmaFinite μ ∧ MeasurableEmbedding (fun q : GinfC Y × GfC Y => (q.1 : GA D Y) * q.2) ∧ ν = (m.prod μ).map (fun q : GinfC Y × GfC Y => (q.1 : GA D Y) * q.2) := by
  intro D Y ν hν
  haveI : LocallyCompactSpace (GinfC Y) := (GlobalTheory.AdelicSplit.isClosed_GinfC' Y).locallyCompactSpace
  haveI : LocallyCompactSpace (GfC Y) := (GlobalTheory.AdelicSplit.isClosed_GfC' Y).locallyCompactSpace
  set e := GlobalTheory.AdelicSplit.splitEquiv Y with he_def
  have he : (⇑e : GinfC Y × GfC Y → GA D Y) = fun q => (q.1 : GA D Y) * q.2 := rfl
  let m₀ : Measure (GinfC Y) := Measure.haar
  let μ : Measure (GfC Y) := Measure.haar
  haveI hρ : ((m₀.prod μ).map e).IsHaarMeasure := ContinuousMulEquiv.isHaarMeasure_map _ e
  set c := Measure.haarScalarFactor ν ((m₀.prod μ).map e) with hc_def
  have hc : ν = c • (m₀.prod μ).map e := Measure.isMulLeftInvariant_eq_smul _ _
  have hc0 : c ≠ 0 := (Measure.haarScalarFactor_pos_of_isHaarMeasure _ _).ne'
  haveI hm : ((c : ℝ≥0∞) • m₀).IsHaarMeasure :=
    Measure.IsHaarMeasure.smul _ (by simpa using hc0) ENNReal.coe_ne_top
  refine ⟨(c : ℝ≥0∞) • m₀, μ, hm, inferInstance, inferInstance, inferInstance, ?_, ?_⟩
  · rw [← he]; exact e.toHomeomorph.measurableEmbedding
  · rw [← he, Measure.prod_smul_left, Measure.map_smul, hc, ENNReal.smul_def]
    exact e.continuous.measurable.aemeasurable

end GlobalTheory.HaarSplit
