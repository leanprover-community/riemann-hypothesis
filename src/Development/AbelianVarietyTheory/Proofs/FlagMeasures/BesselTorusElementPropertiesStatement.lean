module

public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Admissible
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.BesselTorusElementProperties
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open Formalism.FourierDecayAlt GlobalTheory.ThA MeasureTheory Formalism.QuantumDeterminants Matrix
open scoped InnerProductSpace

theorem _root_.GlobalTheory.T.besselTorusElement_properties : ∀ (k r : ℕ) (α : ℂ), α ≠ 0 → aT k r α ∈ B.GV k r ∧ (∀ z, inWb k r z → (∀ h ∈ UWset k r z, aT k r α * h = h * aT k r α) ∧ ∀ n ∈ Nset k r, aT k r α * n * (aT k r α)⁻¹ ∈ Nset k r ∧ (aT k r α)⁻¹ * n * aT k r α ∈ Nset k r ∧ ell k r z (aT k r α * n * (aT k r α)⁻¹) = α * ell k r z n) ∧ (∀ z z', inWb k r z → inWb k r z' → ∀ (g : B.Mat k r) (a b : Fin (r + 1)), Zhat k r z z' ((aT k r α)⁻¹ * g * aT k r α) a b = (star α) ^ (r - a.val) * α ^ (r - b.val) * Zhat k r z z' g a b) ∧ ∀ (c : Fin r → ℂ) (μ : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ), (aT k r α)⁻¹ * bigCell k r c μ * aT k r α = bigCell k r (fun a => ((‖α‖ ^ (2 * (r - a.val)) : ℝ) : ℂ) * c a) μ := by
  first | exact @GlobalTheory.ThA.TorusElt.torusElt | exact GlobalTheory.ThA.TorusElt.torusElt | (intros; apply GlobalTheory.ThA.TorusElt.torusElt <;> assumption)
