module

public import Development.AbelianVarietyTheory.Definitions.Jets.CmLatticeCommutatorPairingPowEqOneOfGoodLift
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.SmallPointMultiplicativeCoordinateExistsUnique
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

open PowerSeries GlobalTheory.MomOne
open scoped ComplexConjugate BigOperators Topology

theorem _root_.GlobalTheory.T.smallPoint_multiplicativeCoordinate_existsUnique : ∀ (q : ℕ) [Fact q.Prime] (M : Mdl q) (ω : ℂ_[q]), M.MChart ω → (∀ ζ : ℂ_[q], ‖ζ - 1‖ < 1 → ∃ p, M.At ω ζ p) ∧ (∀ p, M.Small p → ∃ ζ, M.At ω ζ p) ∧ (∀ ζ ζ' p, M.At ω ζ p → M.At ω ζ' p → ζ = ζ') ∧ (∀ ζ p p', M.At ω ζ p → (M.At ω ζ p' ↔ p - p' ∈ M.L.lattice)) ∧ M.At ω 1 0 := by
  first | exact @GlobalTheory.MomOne.SmallPt.at_exists_unique | exact GlobalTheory.MomOne.SmallPt.at_exists_unique | (intros; apply GlobalTheory.MomOne.SmallPt.at_exists_unique <;> assumption)
