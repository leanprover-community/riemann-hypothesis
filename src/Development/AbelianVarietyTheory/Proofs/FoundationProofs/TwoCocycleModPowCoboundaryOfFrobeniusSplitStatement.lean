module

public import Development.AbelianVarietyTheory.Definitions.Foundations.FinalTheorems
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.TwoCocycleModPowCoboundaryOfFrobeniusSplit
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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

@[expose] public section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix

theorem _root_.GlobalTheory.T.cob2_of_cocycle_cong_of_invariant : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (c : Coef l) (n : ℕ) (D K : Subgroup (G ℚ Ω)) (φ : ↥D) (m : ℕ) (d : ↥D →* Multiplicative (ZMod (m * l ^ n))) (ξ : G ℚ Ω → G ℚ Ω → Qbar l), 0 < m → ((φ ^ m : ↥D) : G ℚ Ω) ∈ K → IsOpen (d.ker : Set ↥D) → (∀ s : ↥D, (((φ ^ (Multiplicative.toAdd (d s)).val)⁻¹ * s : ↥D) : G ℚ Ω) ∈ K) → (∀ k ∈ K, Cg n (eps l k) 1) → (∀ s t, ξ s t ∈ c.O) → (∀ r ∈ D, ∀ s ∈ D, ∀ t ∈ D, Cg n (eps l r * ξ s t + ξ r (s * t)) (ξ (r * s) t + ξ r s)) → (∀ s ∈ D, ∀ t ∈ D, ∀ k ∈ K, Cg n (ξ (s * k) t) (ξ s t) ∧ Cg n (ξ s (t * k)) (ξ s t)) → Cob2 c n D ξ := by
  first | exact @GlobalTheory.Ord2.FrobCob.twoCocycleModPow_coboundary_of_frobenius_split | exact GlobalTheory.Ord2.FrobCob.twoCocycleModPow_coboundary_of_frobenius_split | (intros; apply GlobalTheory.Ord2.FrobCob.twoCocycleModPow_coboundary_of_frobenius_split <;> assumption)
