module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSelfDualFor
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsArchimedeanSchwartzTraceFourierBijective
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
import Mathlib.RingTheory.TotallySplit
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Separation.CompletelyRegular
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.MatchingOfParts
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousAtPlace

@[expose] public section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.WeylFour
open scoped GlobalTheory.VacAny

namespace GlobalTheory.WeylFour


open Classical in
theorem factor_isAddHaar (F : Type) [Field F] [NumberField F] :
    ((Measure.pi fun _ : {w : InfinitePlace F // w.IsReal} => (volume : Measure ℝ)).prod
      (Measure.pi fun _ : {w : InfinitePlace F // w.IsComplex} => (volume : Measure ℂ))).IsAddHaarMeasure :=
  Measure.prod.instIsAddHaarMeasure _ _


open Classical in
instance measI_isAddHaar (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] :
    (measI F κ).IsAddHaarMeasure := by
  haveI := factor_isAddHaar F
  haveI : MeasurableAdd (mixedEmbedding.mixedSpace F) := inferInstance
  exact Measure.pi.isAddHaarMeasure _

theorem eInf_continuous {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]
    (y : κ → mixedEmbedding.mixedSpace F) : Continuous (fun x => eInf x y) := by
  classical
  have hT : Continuous (fun x : κ → mixedEmbedding.mixedSpace F =>
      Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (x ⬝ᵥ y)) :=
    LinearMap.continuous_of_finiteDimensional ((GlobalTheory.ArchFourier.traceDot F κ).flip y)
  unfold eInf
  fun_prop

theorem norm_eInf {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]
    (x y : κ → mixedEmbedding.mixedSpace F) : ‖eInf x y‖ = 1 := by
  unfold eInf
  rw [Complex.norm_exp]
  simp

theorem exists_fourier_measI : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ],
    ∃ ei : SInf F κ →L[ℂ] SInf F κ, Function.Surjective ei ∧ (∀ f y, ei f y = ∫ x, f x * eInf x y ∂(measI F κ)) ∧
      ∀ (f : SInf F κ) y, Continuous (fun x => f x * eInf x y) ∧ Integrable (fun x => f x * eInf x y) (measI F κ) := by
  intro F _ _ κ _
  classical
  haveI : BorelSpace (κ → mixedEmbedding.mixedSpace F) := inferInstance
  haveI : (measI F κ).IsAddHaarMeasure := measI_isAddHaar F κ
  obtain ⟨ei, hb, he⟩ := GlobalTheory.ArchFourier.exists_fourier_sInf F κ (measI F κ)
  refine ⟨ei, hb.2, fun f y => he f y, fun f y => ⟨f.continuous.mul (eInf_continuous y), ?_⟩⟩
  haveI : (measI F κ).HasTemperateGrowth := MeasureTheory.Measure.IsAddHaarMeasure.instHasTemperateGrowth
  have hf : Integrable (fun x => f x) (measI F κ) := f.integrable
  exact hf.mul_bdd (eInf_continuous y).aestronglyMeasurable (Filter.Eventually.of_forall fun x => (norm_eInf x y).le)

end GlobalTheory.WeylFour
