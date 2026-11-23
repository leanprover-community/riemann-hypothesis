module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ActFromBlocks
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralAdelicPureTensorEqProductLocal
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

open scoped Matrix GlobalTheory.VacAny
open NumberField IsDedekindDomain MeasureTheory Filter Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RatWeilOp

theorem _root_.GlobalTheory.T.integral_adelic_pureTensor_eq_product_local : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] [MeasurableSpace (κ → AF F)] [BorelSpace (κ → AF F)]
    [MeasurableSpace (κ → mixedEmbedding.mixedSpace F)] [BorelSpace (κ → mixedEmbedding.mixedSpace F)]
    [∀ v : Pl (F := F), MeasurableSpace (κ → Fv F v)] [∀ v : Pl (F := F), BorelSpace (κ → Fv F v)]
    (μ : Measure (κ → AF F)) [μ.IsAddHaarMeasure] (μi : Measure (κ → mixedEmbedding.mixedSpace F)) [μi.IsAddHaarMeasure]
    (μv : ∀ v : Pl (F := F), Measure (κ → Fv F v)) [∀ v, (μv v).IsAddHaarMeasure],
    (∀ v, μv v {x | ∀ i, x i ∈ v.adicCompletionIntegers F} = 1) → ∃ c : ℂ, c ≠ 0 ∧
      ∀ (f : (κ → mixedEmbedding.mixedSpace F) → ℂ) (φ : ∀ v : Pl (F := F), (κ → Fv F v) → ℂ), Continuous f → Integrable f μi → IsFam φ →
        Integrable (fun x : κ → AF F => f (fun i => evI F (x i)) * ∏ᶠ v, φ v fun i => evFin F v (x i)) μ ∧
        ∫ x, f (fun i => evI F (x i)) * ∏ᶠ v, φ v (fun i => evFin F v (x i)) ∂μ = c * (∫ x, f x ∂μi) * ∏ᶠ v, ∫ x, φ v x ∂(μv v) := by
  first | exact @GlobalTheory.AdelicHaarPure.integral_pure_haar | exact GlobalTheory.AdelicHaarPure.integral_pure_haar | (intros; apply GlobalTheory.AdelicHaarPure.integral_pure_haar <;> assumption)
