module

public import Development.AbelianVarietyTheory.Definitions.Divisors.IsFinSetSplitPlacesCoprimeConductor
public import Mathlib.NumberTheory.NumberField.CMField
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasSumIntegralIdelesEulerProduct
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

open NumberField IsDedekindDomain GlobalTheory.CMVal

theorem _root_.GlobalTheory.T.hasSum_integralIdeles_eulerProduct : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (I : Type) [Fintype I] (φ : I → E →+* ℂ), IsCMType φ → ∀ (s : ℕ) (κ : I → ℕ) (𝔣 : Ideal (OF E)) (Q : Finset (HeightOneSpectrum (OF E))) (χ : HChar E) (Pq : HeightOneSpectrum (OF E) → HeightOneSpectrum (𝓞 E)) (S L : ℂ), UnramFin E → IsBaseCond 𝔣 → IsFinSetSplitPlacesCoprimeConductor 𝔣 Q → IsValChar φ s κ 𝔣 Q χ → (∀ q ∈ Q, Over (Pq q) q) → 1 < S.re → HasProd (eulerFactor χ S) L → open Classical in HasSum (fun z : {z : (Af E)ˣ ⧸ hatOUnits (condQ 𝔣 Q) // ∃ y : (Af E)ˣ, (QuotientGroup.mk y : (Af E)ˣ ⧸ hatOUnits (condQ 𝔣 Q)) = z ∧ (y : Af E) ∈ hatO (condQ 𝔣 Q)} => (finPart χ z.1.out : ℂ) * ((modF z.1.out : ℝ) : ℂ) ^ S) (L * ∏ q ∈ Q.filter (fun q => UnrAt χ (Pq q)), ((1 - (val χ (Pq q) : ℂ) * (Ideal.absNorm q.asIdeal : ℂ) ^ (-S)) * (1 - (val χ (Pq q) : ℂ)⁻¹ * (Ideal.absNorm q.asIdeal : ℂ) ^ (-S)) + ((Ideal.absNorm q.asIdeal : ℂ) - 1) * ((Ideal.absNorm q.asIdeal : ℂ) ^ (-S)) ^ 2)) := by
  first | exact @GlobalTheory.CMVal.Euler.hasSum_euler | exact GlobalTheory.CMVal.Euler.hasSum_euler | (intros; apply GlobalTheory.CMVal.Euler.hasSum_euler <;> assumption)
