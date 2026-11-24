module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeightedMeasureSplitting.ContSplit
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.MeasCore
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicLocalCompactness.AdeleLC
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicLocalCompactness.T2SpaceTensorProductFiniteExtension
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SemidirectVolume.TensTopOf
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeightedMeasureSplitting.T2SpaceGeneralLinearGroup
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
import Mathlib.Topology.Connected.Separation
import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

namespace PI.UnitaryGroupMassFormula.MeasWCore

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures NumberField IsDedekindDomain MeasureTheory
open scoped TensorProduct

theorem map_split_eq {X Y₁ Y₂ : Type} [MeasurableSpace X] [MeasurableSpace Y₁] [MeasurableSpace Y₂]
    {K : Set X} {K₁ : Set Y₁} {K₂ : Set Y₂} (s : X → Y₁ × Y₂) (hs : Measurable s)
    (e : K₁ × K₂ → K) (he : Measurable e) (hse : ∀ p, s (e p : X) = ((p.1 : Y₁), (p.2 : Y₂)))
    (μ₁ : Measure K₁) (μ₂ : Measure K₂) [SFinite μ₁] [SFinite μ₂] :
    (((μ₁.prod μ₂).map e).map Subtype.val).map s = (μ₁.map Subtype.val).prod (μ₂.map Subtype.val) := by
  rw [Measure.map_map measurable_subtype_coe he, Measure.map_map hs (measurable_subtype_coe.comp he),
    Measure.map_prod_map μ₁ μ₂ measurable_subtype_coe measurable_subtype_coe]
  congr 1
  funext p
  exact hse p

theorem mwCore_of (hH : SplitH) (hN : SplitN) (hC : ContSplit) (hS : SProd) :
    Formalism.L2.SG.Pf.MeasCore.MWCore := by
  intro F E _ _ _ _ _ σ n J r P T hCM hJ hP μNinf μHinf hNinf hHinf
  have : Module.Finite F E := PI.VolSemiDirect.W.Lc.finite_nf F E
  obtain ⟨eH, heH⟩ := hH F E σ n J r P T hCM hJ hP
  obtain ⟨eN, heN⟩ := hN F E σ n J r P T hCM hJ hP
  have hsm : Measurable (splitA σ J) := (hC F E σ n J hCM).measurable
  let μHf : Measure (Hsub (Af F) σ J P) := Measure.haar
  let μNf : Measure (Nsub (Af F) σ J P) := Measure.haar
  obtain ⟨μSf, hSH, hSeq⟩ := hS F E σ n J r P T hCM hJ hP μNf μHf inferInstance inferInstance
  have := hHinf
  have := hNinf
  have : SigmaCompactSpace (Hsub (Ainf F) σ J P) := inferInstance
  have : SigmaCompactSpace (Nsub (Ainf F) σ J P) := inferInstance
  have : SigmaCompactSpace (Hsub (Af F) σ J P) := inferInstance
  have : SigmaCompactSpace (Nsub (Af F) σ J P) := inferInstance
  have : SigmaFinite μHinf := inferInstance
  have : SigmaFinite μNinf := inferInstance
  have : SigmaFinite μHf := inferInstance
  have : SigmaFinite μNf := inferInstance
  refine ⟨{ μH := (μHinf.prod μHf).map eH, μHinf := μHinf, μHf := μHf,
            μN := (μNinf.prod μNf).map eN, μNinf := μNinf, μNf := μNf, μSf := μSf,
            μSv := fun v => Measure.haar }, ?_, rfl, rfl⟩
  refine ⟨?_, hHinf, inferInstance, ?_, hNinf, inferInstance, hSH, fun v => inferInstance, ?_, ?_, hSeq⟩
  · exact ContinuousMulEquiv.isHaarMeasure_map (μHinf.prod μHf) eH
  · exact ContinuousMulEquiv.isHaarMeasure_map (μNinf.prod μNf) eN
  · exact map_split_eq (splitA σ J) hsm eH eH.continuous.measurable heH μHinf μHf
  · exact map_split_eq (splitA σ J) hsm eN eN.continuous.measurable heN μNinf μNf

end PI.UnitaryGroupMassFormula.MeasWCore
