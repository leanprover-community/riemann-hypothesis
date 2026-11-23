module

public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.IsLatMeasurableConst
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LineLatticeMeanSinglePairOrbitContribution
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase

theorem _root_.GlobalTheory.T.lineLatticeMean_single_pair_orbit_contribution : ∀ (E : Type) [Field E] [NumberField E], IsTotallyComplex E → ∀ k : ℕ, 1 ≤ k → ∀ Lf : Ideal (𝓞 E) → Submodule (𝓞 E) (Fin k → E) → Submodule (𝓞 E) (Fin (k + 1) → E), (∀ 𝔞 Λ' y, y ∈ Lf 𝔞 Λ' ↔ (∀ t ∈ 𝔞, (t : E) * y 0 ∈ (algebraMap (𝓞 E) E).range) ∧ Fin.tail y ∈ Λ') → ∀ (w : ℝ → ENNReal) (Φ : VecInf E (k + 1) → ENNReal), Measurable w → Measurable Φ → ∀ (𝔞 : Ideal (𝓞 E)) (Λ' : Submodule (𝓞 E) (Fin k → E)), 𝔞 ≠ ⊥ → Submodule.IsFullLattice E Λ' → covol {x | x ∈ autGL E (k + 1) (Lf 𝔞 Λ') ∧ ∀ w a, x w a 0 = if a = 0 then 1 else 0} ((haarGL E (k + 1)).withDensity fun g => w (covAt E (k + 1) (latAt E (k + 1) (Lf 𝔞 Λ') g)) * Φ (fun u a => (Matrix.of (g u))⁻¹ a 0)) {g | 0 < detNorm E (k + 1) g} = slabVol E k Λ' * ENNReal.ofReal (Formalism.HermitianLatticesTheory.vInv E ^ (Formalism.HermitianLatticesTheory.fDeg E * (2 * k + 1)) * ((Ideal.absNorm 𝔞 : ℝ) ^ (k + 1))⁻¹) * (∫⁻ x, Φ x) * ∫⁻ t in Set.Ioi (0 : ℝ), w t / ENNReal.ofReal (t ^ 2) := by
  first | exact @GlobalTheory.OrbitTerm.orbit_term | exact GlobalTheory.OrbitTerm.orbit_term | (intros; apply GlobalTheory.OrbitTerm.orbit_term <;> assumption)
