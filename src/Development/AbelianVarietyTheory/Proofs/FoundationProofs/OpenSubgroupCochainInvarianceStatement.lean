module

public import Development.AbelianVarietyTheory.Definitions.Foundations.FinalTheorems
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.ResMapBijective
public import Mathlib.RingTheory.AdicCompletion.Noetherian
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.OpenSubgroupCochainInvariance
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
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix

theorem _root_.GlobalTheory.T.open_subgroup_cochain_invariance : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (n : ℕ) (H I : Subgroup (G ℚ Ω)) (ξ : G ℚ Ω → G ℚ Ω → Qbar l), IsClosed (H : Set (G ℚ Ω)) → I ≤ H → ContinuousOn (fun p : G ℚ Ω × G ℚ Ω => ξ p.1 p.2) ((H : Set (G ℚ Ω)) ×ˢ (H : Set (G ℚ Ω))) → (∀ i ∈ I, eps l i = 1) → (∀ s ∈ H, ∀ t ∈ H, ∀ i ∈ I, Cg n (ξ (s * i) t) (ξ s t) ∧ Cg n (ξ s (t * i)) (ξ s t)) → ∃ K : Subgroup (G ℚ Ω), I ≤ K ∧ K ≤ H ∧ IsOpen ((K.subgroupOf H : Subgroup ↥H) : Set ↥H) ∧ (∀ k ∈ K, Cg n (eps l k) 1) ∧ ∀ s ∈ H, ∀ t ∈ H, ∀ k ∈ K, Cg n (ξ (s * k) t) (ξ s t) ∧ Cg n (ξ s (t * k)) (ξ s t) := by
  first | exact @GlobalTheory.Ord2.OpenInv.open_inv | exact GlobalTheory.Ord2.OpenInv.open_inv | (intros; apply GlobalTheory.Ord2.OpenInv.open_inv <;> assumption)
