module

public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.LocalRing.ResidueField.Defs
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsIntegralUnitPairingOfIrreducibleReductionA
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
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.PolyApproxZeroPadic

@[expose] public section

open GlobalTheory.Cong

theorem _root_.GlobalTheory.T.exists_integral_unit_pairing_of_irreducible_residue : ∀ (R k : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field k] [Algebra R k] [IsFractionRing R k] (a : ℕ) (B : Matrix (Fin a) (Fin a) R), (∀ W : Submodule (IsLocalRing.ResidueField R) (Fin a → IsLocalRing.ResidueField R), (∀ v ∈ W, (B.map (IsLocalRing.residue R)).mulVec v ∈ W) → W = ⊥ ∨ W = ⊤) → ∀ W : Submodule k (Fin a → k), W ≠ ⊥ → W ≠ ⊤ → ∃ w f : Fin a → R, (fun i => algebraMap R k (w i)) ∈ W ∧ (∀ y ∈ W, (fun i => algebraMap R k (f i)) ⬝ᵥ y = 0) ∧ IsUnit (f ⬝ᵥ B.mulVec w) := by
  first | exact @GlobalTheory.Cong.exists_integral_unit_pairing_of_irreducible_reduction | exact GlobalTheory.Cong.exists_integral_unit_pairing_of_irreducible_reduction | (intros; apply GlobalTheory.Cong.exists_integral_unit_pairing_of_irreducible_reduction; all_goals assumption)
