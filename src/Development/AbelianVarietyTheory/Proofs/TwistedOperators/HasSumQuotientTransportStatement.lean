module

public import Mathlib.Analysis.CStarAlgebra.Classes
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasSumQuotientTransport
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

@[expose] public section


theorem _root_.GlobalTheory.T.hasSum_quotient_of_hasSum_mulEquiv_quotient : ∀ (G H : Type) [Group G] [Group H] (e : G ≃* H) (K : Subgroup G) (K' : Subgroup H), (∀ g, g ∈ K ↔ e g ∈ K') → ∀ f : G → ℂ, (∀ g, ∀ k ∈ K, f (g * k) = f g) → ∀ s : ℂ, HasSum (fun b : H ⧸ K' => f (e.symm b.out)) s → HasSum (fun a : G ⧸ K => f a.out) s := by
  first | exact @GlobalTheory.hasSum_quotient_transport | exact GlobalTheory.hasSum_quotient_transport | (intros; apply GlobalTheory.hasSum_quotient_transport <;> assumption)
