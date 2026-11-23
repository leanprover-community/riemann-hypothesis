module

public import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.InitialLengthsProductMomentLe
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
import Formalism.HermitianCurvature.BesselNonvanishingReduction
import Formalism.HermitianCurvature.StatementI

@[expose] public section

open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

theorem _root_.GlobalTheory.T.initial_lengths_product_moment_le : ∀ (Ω : Type) [MeasurableSpace Ω] (ν : Measure Ω) (r l : ℕ) (hl : l ≤ r + 1) (len : Fin (r + 1) → Ω → ℝ) (Ph : Ω → ℝ) (A Rr : ℝ), (∀ a, AEMeasurable (len a) ν) → (∀ a, ∀ᵐ x ∂ν, 0 < len a x) → AEMeasurable Ph ν → (∀ x, 0 ≤ Ph x) → ∫⁻ x, ENNReal.ofReal (Ph x) ∂ν = 1 → 0 ≤ A → 1 ≤ Rr → (∀ q ≤ (r + 1) ^ 2, ∫⁻ x, ENNReal.ofReal (len 0 x ^ (2 * q) * Ph x) ∂ν ≤ ENNReal.ofReal (A ^ q)) → (∀ a : Fin r, ∀ q ≤ (r + 1) ^ 2, ∫⁻ x, ENNReal.ofReal ((len a.succ x / len a.castSucc x) ^ (2 * q) * Ph x) ∂ν ≤ ENNReal.ofReal (Rr ^ (2 * q))) → ∫⁻ x, ENNReal.ofReal ((∏ a : Fin l, len (Fin.castLE hl a) x ^ 2) * Ph x) ∂ν ≤ ENNReal.ofReal ((A * Rr ^ (2 * r)) ^ l) := by
  first | exact @GlobalTheory.MomentHolder.initial_product_moment_le | exact GlobalTheory.MomentHolder.initial_product_moment_le | (intros; apply GlobalTheory.MomentHolder.initial_product_moment_le <;> assumption)
