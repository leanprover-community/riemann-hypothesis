module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InvMemIntV
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormStepIntegrality
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRootSelectionUnitaryRankOne

@[expose] public section

open Matrix NumberField IsDedekindDomain GlobalTheory.LKTrip GlobalTheory.LKMid GlobalTheory.OrbFinAf
open scoped TensorProduct Classical

theorem _root_.GlobalTheory.T.integral_order_centralizer_stable : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (v : AwayP p) (g : (Qv v ⊗[ℚ] G.C)ˣ) (c : (Qv v)ˣ), (g : Qv v ⊗[ℚ] G.C) * (starT G.star (Qv v) g).unop = algebraMap (Qv v) (Qv v ⊗[ℚ] G.C) c → IsIntV G v 1 → (∀ y z : Qv v ⊗[ℚ] G.C, IsIntV G v y → IsIntV G v z → IsIntV G v (y * z)) → (∀ y : Qv v ⊗[ℚ] G.C, IsIntV G v y → IsIntV G v (starT G.star (Qv v) y).unop) → (∀ y z : Qv v ⊗[ℚ] G.C, y * g = g * y → z * g = g * z → y * z = z * y) → ∀ θ θ' h : Qv v ⊗[ℚ] G.C, θ * g = g * θ → θ' * g = g * θ' → h * g = g * h → IsIntV G v θ → IsIntV G v θ' → IsIntV G v h → (θ - (starT G.star (Qv v) θ).unop) * θ' = 1 → 2 * h = 1 → ∀ s : (Qv v ⊗[ℚ] G.C)ˣ, s * g = g * s → IsIntV G v (s : Qv v ⊗[ℚ] G.C) → IsIntV G v ((s⁻¹ : (Qv v ⊗[ℚ] G.C)ˣ) : Qv v ⊗[ℚ] G.C) → (starT G.star (Qv v) s).unop = s → ∃ u : (Qv v ⊗[ℚ] G.C)ˣ, u * g = g * u ∧ IsIntV G v (u : Qv v ⊗[ℚ] G.C) ∧ IsIntV G v ((u⁻¹ : (Qv v ⊗[ℚ] G.C)ˣ) : Qv v ⊗[ℚ] G.C) ∧ (u : Qv v ⊗[ℚ] G.C) * (starT G.star (Qv v) u).unop = s := by
  first | (exact @GlobalTheory.OrbFinAf.normStep_exists) | (exact GlobalTheory.OrbFinAf.normStep_exists) | (intros; apply GlobalTheory.OrbFinAf.normStep_exists  <;> assumption)
