module

public import Development.AbelianVarietyTheory.Definitions.Foundations.FinalTheorems
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.ResMapBijective
public import Mathlib.RingTheory.AdicCompletion.Noetherian
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsFrobeniusPowInvMulMemOpenSubgroup
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

theorem _root_.GlobalTheory.T.exists_frobenius_pow_inv_mul_mem_open_subgroup : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (q : Pl) (B : ValuationSubring Ω) (K : Subgroup (G ℚ Ω)), IsPlaceOver B q → Ine (F := ℚ) B ≤ K → IsOpen ((K.subgroupOf (Dec (F := ℚ) B) : Subgroup ↥(Dec (F := ℚ) B)) : Set ↥(Dec (F := ℚ) B)) → ∃ (φ : ↥(Dec (F := ℚ) B)) (m : ℕ), 0 < m ∧ ((φ ^ m : ↥(Dec (F := ℚ) B)) : G ℚ Ω) ∈ K ∧ ∀ N : ℕ, 0 < N → ∃ d : ↥(Dec (F := ℚ) B) →* Multiplicative (ZMod (m * N)), IsOpen (d.ker : Set ↥(Dec (F := ℚ) B)) ∧ ∀ s : ↥(Dec (F := ℚ) B), (((φ ^ (Multiplicative.toAdd (d s)).val)⁻¹ * s : ↥(Dec (F := ℚ) B)) : G ℚ Ω) ∈ K := by
  first | exact @GlobalTheory.Ord2.exists_frob_pow_inv_mul_mem | exact GlobalTheory.Ord2.exists_frob_pow_inv_mul_mem | (intros; apply GlobalTheory.Ord2.exists_frob_pow_inv_mul_mem <;> assumption)
