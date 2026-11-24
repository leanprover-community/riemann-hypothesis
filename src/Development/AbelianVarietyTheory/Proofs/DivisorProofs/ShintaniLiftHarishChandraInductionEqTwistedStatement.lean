module

public import Development.AbelianVarietyTheory.Definitions.Divisors.OrthSubrepresentation
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ShintaniLiftHarishChandraInductionEqTwisted
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
import Development.AbelianVarietyTheory.Definitions.CommutativeAlgebra.AbByPOfComm

@[expose] public section

open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical

theorem _root_.GlobalTheory.T.shintaniLift_harishChandraInduction_eq_twisted : ∀ (F F' : Type) [Field F] [Field F'] [Algebra F F'] [Finite F'] (s : F' ≃ₐ[F] F'), (∀ t : F' ≃ₐ[F] F', t ∈ Subgroup.zpowers s) → ∀ (a b n : ℕ), n = a + b → ∀ (α : GL (Fin a) F → ℂ) (β : GL (Fin b) F → ℂ), IsCl α → IsCl β → shLift s (hc a b α β n) = hcTw (s : F' →+* F') a b (shLift s α) (shLift s β) n := by
  first | (exact @GlobalTheory.Shin.shLift_hc_eq_hcTw) | (exact GlobalTheory.Shin.shLift_hc_eq_hcTw) | (intros; apply GlobalTheory.Shin.shLift_hc_eq_hcTw  <;> assumption)
