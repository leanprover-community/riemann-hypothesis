module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsGauss
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GaussNormAcrisSubUnitLeDigit
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

@[expose] public section

open GlobalTheory.PMon.Gauss
open scoped Formalism.Per

theorem _root_.GlobalTheory.T.gaussNormAcris_sub_unit_le_digit : ∀ (l : ℕ) [Fact l.Prime] (h s : ℕ), s < h → ∀ w w' : Formalism.Per.Acris l, (φc l)^[h] w' = (l : Formalism.Per.Acris l) ^ s * w' → w' ≠ 0 → φc l w * w' = w * φc l w' → (∀ ρ : ℝ, (l : ℝ)⁻¹ ≤ ρ → ρ < 1 → gC l ρ w = gC l ρ w') → ∃ c : ℤ_[l], IsUnit c ∧ ∀ ρ : ℝ, (l : ℝ)⁻¹ ≤ ρ → ρ < 1 → gC l ρ (w - zc l c * w') ≤ ρ * gC l ρ w' := by
  first | exact @GlobalTheory.PMon.Gauss.one_digit | exact GlobalTheory.PMon.Gauss.one_digit | (intros; apply GlobalTheory.PMon.Gauss.one_digit <;> assumption)
