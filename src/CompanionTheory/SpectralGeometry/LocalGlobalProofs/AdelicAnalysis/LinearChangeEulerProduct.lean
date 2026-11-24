module

public import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.CompletionIsLocalRing
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.GlobalUnitScalingHaarProductFormula
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.MeasureTheory.Group.Measure
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.HaarMapLinearScalingByDeterminant
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicLocalCompactness.AdeleLC
import GroundTheory.GlobalFields.LocalAtPlace
import GroundTheory.GlobalFields.LocalFieldAtPlace
import GroundTheory.GlobalFields.TateThesis.AdeleMeasurable
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
import Mathlib.Tactic.Linter.HaveILetI
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

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

namespace GlobalTheory.CompanionTheory.SW.ProdFormula

theorem modulus_matrix : ∀ (F : Type) [Field F] [NumberField F] (ι : Type) [Fintype ι] [DecidableEq ι] (A : Matrix ι ι F), A.det ≠ 0 → ∃ (cinf : ℝ≥0) (c : HeightOneSpectrum (𝓞 F) → ℝ≥0), IsUnitProd cinf c ∧ (∀ μ : Measure (ι → Ainf F), μ.IsAddHaarMeasure → μ.map (fun x => A.map (algebraMap F (Ainf F)) *ᵥ x) = cinf • μ) ∧ ∀ v : HeightOneSpectrum (𝓞 F), (∀ μ : Measure (ι → Fv F v), μ.IsAddHaarMeasure → μ.map (fun x => A.map (algebraMap F (Fv F v)) *ᵥ x) = c v • μ) := by
  intro F _ _ ι _ _ A hA
  obtain ⟨cinf, c, hU, hinf, hv⟩ := _root_.GlobalTheory.CompanionTheory.SW.ProdFormula.unitProd_scalar F A.det hA
  refine ⟨cinf, c, hU, ?_, ?_⟩
  · intro μ hμ
    haveI : BorelSpace (Ainf F) := ⟨rfl⟩
    exact _root_.GlobalTheory.CompanionTheory.SW.DetScale.map_mulVec_eq_smul F (Ainf F) ι A hA Measure.addHaar inferInstance cinf
      (hinf Measure.addHaar inferInstance) μ hμ
  · intro v μ hμ
    haveI : BorelSpace (Fv F v) := ⟨rfl⟩
    haveI : SecondCountableTopology (Fv F v) := (GlobalTheory.CompanionTheory.SW.LocFv.isLocR_Fv F v).2.2.1
    exact _root_.GlobalTheory.CompanionTheory.SW.DetScale.map_mulVec_eq_smul F (Fv F v) ι A hA Measure.addHaar inferInstance (c v)
      (hv v Measure.addHaar inferInstance) μ hμ

end GlobalTheory.CompanionTheory.SW.ProdFormula
