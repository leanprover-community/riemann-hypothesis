module

public import Development.AbelianVarietyTheory.Definitions.Divisors.SimpleTwistedTraceFormulaStable
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedOrbitalIntegralEqSumSmallerLevel
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

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC GlobalTheory.BCT
open scoped Classical TensorProduct

theorem _root_.GlobalTheory.T.twistedOrbitalIntegral_eq_sum_smallerLevel : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (θ : G →* G) (K : Subgroup G), IsOpen (K : Set G) → IsCompact (K : Set G) → (∀ k ∈ K, θ k ∈ K) → ∀ K' : Subgroup G, IsLevel θ K K' → ∀ (δ : G) (f : G → ℂ), IsHecke K' f → (∀ x : G, twCent θ δ ⊓ K.map (MulAut.conj x).toMonoidHom ≤ cptPart (twCent θ δ) ∧ (twCent θ δ ⊓ K'.map (MulAut.conj x).toMonoidHom).relIndex (cptPart (twCent θ δ)) ≠ 0) → {q : DoubleCoset.Quotient (twCent θ δ : Set G) (K' : Set G) | f ((Quotient.out q)⁻¹ * δ * θ (Quotient.out q)) ≠ 0}.Finite → twOrb θ K δ f = ((K'.relIndex K : ℕ) : ℂ)⁻¹ * twOrb θ K' δ f ∧ twOrb θ K' δ f = ∑ᶠ q : DoubleCoset.Quotient (twCent θ δ : Set G) (K' : Set G), (((twCent θ δ ⊓ K'.map (MulAut.conj (Quotient.out q)).toMonoidHom).relIndex (cptPart (twCent θ δ)) : ℕ) : ℂ) * f ((Quotient.out q)⁻¹ * δ * θ (Quotient.out q)) := by
  first | exact @GlobalTheory.BCT.OrbLev.twOrb_eq_sum_smallerLevel | exact GlobalTheory.BCT.OrbLev.twOrb_eq_sum_smallerLevel | (intros; apply GlobalTheory.BCT.OrbLev.twOrb_eq_sum_smallerLevel <;> assumption)
