module

public import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LintegralProdPowLeOfMomentsMassLeOne
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.MomAllP
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.OnePlaceKF
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.UpperOff

@[expose] public section

open BranchingSupport GlobalTheory.CellAmp GlobalTheory.Amp GlobalTheory.TypeAsm Formalism.BasicNotions Formalism.MainNotions.S Formalism.QuantumDeterminants Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

theorem _root_.GlobalTheory.T.lintegral_prod_pow_le_of_moments_mass_le_one : ∀ (Ω : Type) [MeasurableSpace Ω] (ν : Measure Ω) (r q : ℕ) (ρ : Fin r → Ω → ℝ) (Ph : Ω → ℝ) (Rr : ℝ) (s : Finset (Fin r)), (∀ a, AEMeasurable (ρ a) ν) → (∀ a, ∀ᵐ x ∂ν, 0 ≤ ρ a x) → AEMeasurable Ph ν → (∀ x, 0 ≤ Ph x) → ∫⁻ x, ENNReal.ofReal (Ph x) ∂ν ≤ 1 → 1 ≤ Rr → (∀ a, ∫⁻ x, ENNReal.ofReal (ρ a x ^ (2 * (r * q)) * Ph x) ∂ν ≤ ENNReal.ofReal (Rr ^ (2 * (r * q)))) → ∫⁻ x, ENNReal.ofReal ((∏ a ∈ s, ρ a x) ^ (2 * q) * Ph x) ∂ν ≤ ENNReal.ofReal (Rr ^ (2 * (r * q))) := by
  first | exact @GlobalTheory.lintegral_prod_pow_le_of_moments | exact GlobalTheory.lintegral_prod_pow_le_of_moments | (intros; apply GlobalTheory.lintegral_prod_pow_le_of_moments <;> assumption)
