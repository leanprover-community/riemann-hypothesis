module

public import Mathlib.Basic.Complex.Basic
public import Mathlib.GroupTheory.SemidirectProduct
public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FourierSumsCosetsSemidirectCyclic
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
import Development.AbelianVarietyTheory.Definitions.CommutativeAlgebra.InvariantSubspaceMobiusInverseRecEqOfFinrankLt
import Development.AbelianVarietyTheory.Definitions.Divisors.OrthSubrepresentation

@[expose] public section

open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical

theorem _root_.GlobalTheory.T.fourier_sums_cosets_semidirect_cyclic : ∀ (G Γ : Type) [Group G] [Finite G] [Group Γ] [Fintype Γ] (φ : Γ →* MulAut G) (s : Γ), (∀ t : Γ, t ∈ Subgroup.zpowers s) → ∀ ζ : ℂ, IsPrimitiveRoot ζ (Nat.card Γ) → ∃ η : G ⋊[φ] Γ →* ℂˣ, (∀ g, η (inl g) = 1) ∧ (η (inr s) : ℂ) = ζ ∧ ∀ X Y : G ⋊[φ] Γ → ℂ, ((Nat.card Γ : ℂ) * ∑ᶠ g, X (inl g) * star (Y (inl g)) = ∑ a ∈ Finset.range (Nat.card Γ), ∑ᶠ x, X x * star (Y x * (η x : ℂ) ^ a)) ∧ (Nat.card Γ : ℂ) * ∑ᶠ g, X (inl g * inr s) * star (Y (inl g * inr s)) = ∑ a ∈ Finset.range (Nat.card Γ), ζ ^ a * ∑ᶠ x, X x * star (Y x * (η x : ℂ) ^ a) := by
  first | (exact @GlobalTheory.Shin.CosetFourier.fourier_coset_sums) | (exact GlobalTheory.Shin.CosetFourier.fourier_coset_sums) | (intros; apply GlobalTheory.Shin.CosetFourier.fourier_coset_sums  <;> assumption)
