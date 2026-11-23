module

public import Development.AbelianVarietyTheory.BlockTheory.SiegelWeilLocal.CenteredPerpendicularSets
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsStabilizerNilradicalLiftOfIsotropic
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

open GlobalTheory.Count GlobalTheory.IndefiniteRowSideFullHecke.CenteredPerpendicularSets Formalism.MainNotions.S Formalism.HN Formalism.REAL Matrix NumberField Finset

theorem _root_.GlobalTheory.T.exists_stabilizerNilradical_lift_of_isotropic : ∀ (n : ℕ) (ε : Fin n → Bool) (H G D : Matrix (Fin n) (Fin n) ℂ) (W : Submodule ℂ (Fin n → ℂ)), IsUnit G.det → Gᴴ * H * G = Jm ε → (∀ u ∈ W, u ∈ perpSet (starRingEnd ℂ) H W) → (∀ u ∈ W, D *ᵥ u = 0) → (∀ u ∈ perpSet (starRingEnd ℂ) H W, D *ᵥ u ∈ W) → ∃ A : Matrix (Fin n) (Fin n) ℂ, InNil (starRingEnd ℂ) H W A ∧ (∀ u ∈ perpSet (starRingEnd ℂ) H W, A *ᵥ u = D *ᵥ u) ∧ hs (G⁻¹ * A * G) ≤ 2 * hs (G⁻¹ * D * G) := by
  first | exact @GlobalTheory.NilLift.exists_lift | exact GlobalTheory.NilLift.exists_lift | (intros; apply GlobalTheory.NilLift.exists_lift <;> assumption)
