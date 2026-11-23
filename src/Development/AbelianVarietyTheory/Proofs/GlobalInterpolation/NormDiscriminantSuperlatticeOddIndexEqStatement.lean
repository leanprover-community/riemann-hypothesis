module

public import Development.AbelianVarietyTheory.Definitions.Jets.CmLatticeCommutatorPairingPowEqOneOfGoodLift
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.NormDiscriminantSuperlatticeOddIndexEq
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.LatIntZero

@[expose] public section

open GlobalTheory.MomOne GlobalTheory.MomN PowerSeries
open scoped ComplexConjugate

theorem _root_.GlobalTheory.T.norm_discriminant_superlattice_odd_index_eq : ∀ (q : ℕ) [Fact q.Prime] (M : Mdl q) (L' : PeriodPair) (N : ℕ), q ≠ 2 → M.Ok → Nat.Coprime N (2 * q) → M.L.lattice ≤ L'.lattice → (∀ x ∈ L'.lattice, (N : ℂ) * x ∈ M.L.lattice) → ‖M.ι (L'.g₂ ^ 3 - 27 * L'.g₃ ^ 2)‖ = ‖M.ι (M.L.g₂ ^ 3 - 27 * M.L.g₃ ^ 2)‖ := by
  first | exact @GlobalTheory.MomDisc.norm_disc_eq | exact GlobalTheory.MomDisc.norm_disc_eq | (intros; apply GlobalTheory.MomDisc.norm_disc_eq <;> assumption)
