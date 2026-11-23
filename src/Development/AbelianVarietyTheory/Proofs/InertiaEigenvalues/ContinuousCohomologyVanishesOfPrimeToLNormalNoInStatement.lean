module

public import Mathlib.Topology.Algebra.Group.ContinuousInv
public import ReciprocityTheory.GaloisValuations.SeparatedDvrSecondCohomologyMem
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ContinuousCohomologyVanishesOfPrimeToLNormalNoIn
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

open ReciprocityTheory.Gal

theorem _root_.GlobalTheory.T.continuousCohomology_vanishes_of_primeToL_normal_no_invariants : ∀ (Γ : Type) [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CompactSpace Γ] [T2Space Γ] [TotallyDisconnectedSpace Γ] (R M : Type) [CommRing R] [AddCommGroup M] [Module R M] [TopologicalSpace M] [DiscreteTopology M] [ContinuousConstSMul R M] (ρ : Representation R Γ M) (l : ℕ) (J : Subgroup Γ), l.Prime → J.Normal → IsClosed (J : Set Γ) → (∀ U : Subgroup Γ, U.Normal → IsOpen (U : Set Γ) → ∀ j ∈ J, ∃ n, Nat.Coprime n l ∧ j ^ n ∈ U) → ContAction ρ → (∀ m : M, ∃ n, l ^ n • m = 0) → (∀ m : M, (∀ j ∈ J, ρ j m = m) → m = 0) → H0 ρ = ⊥ ∧ Subsingleton (H1 ρ) ∧ Subsingleton (H2 ρ) := by
  first | exact @GlobalTheory.PrimeToNormalVanishing.cohomology_vanishes | exact GlobalTheory.PrimeToNormalVanishing.cohomology_vanishes | (intros; apply GlobalTheory.PrimeToNormalVanishing.cohomology_vanishes <;> assumption)
