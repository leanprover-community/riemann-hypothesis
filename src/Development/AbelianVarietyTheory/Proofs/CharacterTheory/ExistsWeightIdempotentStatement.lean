module

public import Mathlib.RepresentationTheory.Basic
public import Development.AbelianVarietyTheory.Proofs.CharacterTheory.ExistsWeightIdempotent
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

@[expose] public section


theorem _root_.GlobalTheory.T.exists_weight_idempotent_of_eigenvector : ∀ (L : Type) [Field L] [CharZero L] (G : Type) [Group G] [Finite G] (V : Type) [AddCommGroup V] [Module L V] (ρ : Representation L G V) (B T : Subgroup G) (lam : B →* Lˣ) (v : V), B.Normal → v ≠ 0 → (∀ b : B, ρ b v = (lam b : L) • v) → (∀ g : G, g ∈ T ↔ ∀ b b' : B, (b' : G) = g⁻¹ * b * g → lam b' = lam b) → ∃ e : Module.End L V, e ≠ 0 ∧ e * e = e ∧ (∀ b : B, ρ b * e = (lam b : L) • e) ∧ (∀ t ∈ T, ρ t * e = e * ρ t) ∧ ∀ g ∉ T, e * ρ g * e = 0 := by
  first | exact @GlobalTheory.exists_weight_idempotent | exact GlobalTheory.exists_weight_idempotent | (intros; apply GlobalTheory.exists_weight_idempotent <;> assumption)
