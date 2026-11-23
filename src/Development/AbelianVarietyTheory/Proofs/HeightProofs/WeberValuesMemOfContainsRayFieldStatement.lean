module

public import Development.AbelianVarietyTheory.Definitions.HeightFunctions.XiValIffXiAt
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.RayFieldTheta
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.WeberValuesMemOfContainsRayField
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
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open NumberField IsDedekindDomain GlobalTheory.FieldSize
open scoped IntermediateField

theorem _root_.GlobalTheory.T.weberValues_mem_of_containsRayField : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] (φ : K →+* L) (ψ : L →+* ℂ), Module.finrank ℚ K = 2 → (∃ a : K, a ^ 2 = -(H.d : K)) → ∀ n : ℕ, 3 ≤ n → GlobalTheory.IndefiniteRowSideFullHecke.RayFieldTheta.ContainsRayField φ n → GlobalTheory.FinalJoin.WeberIn H ψ.toRatAlgHom.fieldRange n ∧ H.rt0 ∈ ψ.toRatAlgHom.fieldRange := by
  first | exact @GlobalTheory.FieldSize.WeberTransport.weberIn_of_containsRayField | exact GlobalTheory.FieldSize.WeberTransport.weberIn_of_containsRayField | (intros; apply GlobalTheory.FieldSize.WeberTransport.weberIn_of_containsRayField <;> assumption)
