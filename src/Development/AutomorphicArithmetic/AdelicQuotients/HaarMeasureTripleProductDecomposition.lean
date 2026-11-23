module

public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Development.AbelianVarietyTheory.Definitions.Foundations.MeasurePreservingRmulQuotMeas
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
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
import Development.AbelianVarietyTheory.Definitions.Foundations.NormEulerPolySubOneLe
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.SchurStep
import Development.WeilBound.ThetaLifts.LatticeBasics.EulerA
public import Mathlib.MeasureTheory.Measure.Haar.Unique

@[expose] public section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.Dbl GlobalTheory.PRep Formalism.BasicNotions UpperTheory.TP

theorem UpperTheory.haarMeasure_triple_product_decomposition :
    ∀ {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G] (A B C : Subgroup G), IsClosed (A : Set G) → IsClosed (B : Set G) → IsClosed (C : Set G) → ∀ (j : A × B × C ≃ₜ* G) (μ : Measure G), μ.IsHaarMeasure → ∀ (μA : Measure A) (μB : Measure B) (μC : Measure C), μA.IsHaarMeasure → μB.IsHaarMeasure → μC.IsHaarMeasure → ∀ f : G → ℂ, Integrable f μ → Integrable (fun y => f (j y)) (μA.prod (μB.prod μC)) ∧ ∃ c : ℝ, ∫ y, f (j y) ∂(μA.prod (μB.prod μC)) = c * ∫ g, f g ∂μ := by
  intro G _ _ _ _ _ _ _ _ A B C hA hB hC j μ hμ μA μB μC hμA hμB hμC f hf
  haveI : LocallyCompactSpace A := hA.isClosedEmbedding_subtypeVal.locallyCompactSpace
  haveI : LocallyCompactSpace B := hB.isClosedEmbedding_subtypeVal.locallyCompactSpace
  haveI : LocallyCompactSpace C := hC.isClosedEmbedding_subtypeVal.locallyCompactSpace
  haveI : (μB.prod μC).IsHaarMeasure := Measure.prod.instIsHaarMeasure μB μC
  haveI : SigmaFinite (μB.prod μC) := inferInstance
  haveI : MeasurableMul (B × C) := inferInstance
  haveI hPH : (μA.prod (μB.prod μC)).IsHaarMeasure :=
    Measure.prod.instIsHaarMeasure μA (μB.prod μC)
  set P : Measure (A × B × C) := μA.prod (μB.prod μC) with hP
  have hme : MeasurableEmbedding j := j.toHomeomorph.measurableEmbedding
  haveI hmap : (Measure.map j P).IsHaarMeasure := ContinuousMulEquiv.isHaarMeasure_map P j
  have hk : Measure.map j P = Measure.haarScalarFactor (Measure.map j P) μ • μ :=
    Measure.isMulLeftInvariant_eq_smul _ _
  set k : ℝ≥0 := Measure.haarScalarFactor (Measure.map j P) μ with hkdef
  have hfm : Integrable f (Measure.map j P) := by
    rw [hk]; exact hf.smul_measure (by simp)
  refine ⟨?_, (k : ℝ), ?_⟩
  · exact (hme.integrable_map_iff).1 hfm
  · have h1 : ∫ g, f g ∂(Measure.map j P) = ∫ y, f (j y) ∂P := hme.integral_map f
    rw [← h1, hk, integral_smul_nnreal_measure]
    simp [NNReal.smul_def]
