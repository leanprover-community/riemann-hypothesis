module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AlgebraMapConeRing
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
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar

@[expose] public section

open CrystallineSemistableComparison.Onto GlobalTheory.CompanionTheory.SurjectionOntoH4

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.CompanionTheory.SurjectionOntoH4.Away

variable {K : Type} [Field K] {n d : ℕ}

theorem mon_pow {M : AddSubmonoid (Gam n d)} (c : Gam n d) (hc : c ∈ M) (N : ℕ) :
    mon K c hc ^ N = mon K (N • c) (M.nsmul_mem hc N) := by
  simp only [mon, AddMonoidAlgebra.single_pow, one_pow]
  rfl

theorem incl_injective {M M' : AddSubmonoid (Gam n d)} (h : M ≤ M') :
    Function.Injective (incl (K := K) h) := by
  intro x y hxy
  simp only [incl, AddMonoidAlgebra.mapDomainAlgHom_apply] at hxy
  exact AddMonoidAlgebra.mapDomain_injective (AddSubmonoid.inclusion_injective h) hxy

theorem exists_mul_pow_eq_incl {M M' : AddSubmonoid (Gam n d)} (h : M ≤ M') (c : Gam n d) (hc : c ∈ M)
    (hg : ∀ g ∈ M', ∃ N : ℕ, g + N • c ∈ M) (z : Rg K M') :
    ∃ (N : ℕ) (a : Rg K M), z * incl h (mon K c hc ^ N) = incl h a := by
  induction z using AddMonoidAlgebra.induction_linear with
  | zero => exact ⟨0, 0, by simp⟩
  | add f g hf hg' =>
    obtain ⟨N₁, a₁, h₁⟩ := hf
    obtain ⟨N₂, a₂, h₂⟩ := hg'
    refine ⟨N₁ + N₂, a₁ * mon K c hc ^ N₂ + a₂ * mon K c hc ^ N₁, ?_⟩
    rw [map_add (f := _), map_mul, map_mul, ← h₁, ← h₂, pow_add, map_mul]
    ring
  | single m k =>
    obtain ⟨N, hN⟩ := hg m.1 m.2
    refine ⟨N, AddMonoidAlgebra.single ⟨m.1 + N • c, hN⟩ k, ?_⟩
    rw [mon_pow, incl_mon]
    simp only [mon, incl, AddMonoidAlgebra.mapDomainAlgHom_apply, AddMonoidAlgebra.single_mul_single, mul_one]
    simp
    rfl

theorem isLocalization_away : ∀ {K : Type} [Field K] {n d : ℕ} {M M' : AddSubmonoid (Gam n d)} (h : M ≤ M') (c : Gam n d) (hc : c ∈ M), -c ∈ M' → (∀ g ∈ M', ∃ N : ℕ, g + N • c ∈ M) → letI := (incl (K := K) h).toRingHom.toAlgebra; IsLocalization.Away (mon K c hc) (Rg K M') := by
  intro K _ n d M M' h c hc hneg hg
  letI := (incl (K := K) h).toRingHom.toAlgebra
  have hal : ∀ x, algebraMap (Rg K M) (Rg K M') x = incl h x := fun _ => rfl
  have hu : IsUnit (incl h (mon K c hc)) := by
    rw [incl_mon]
    refine IsUnit.of_mul_eq_one (mon K (-c) hneg) ?_
    rw [mon_mul]
    simp only [mon, add_neg_cancel]
    rfl
  refine (isLocalization_iff _ _).2 ⟨?_, fun z => ?_, fun {x y} hxy => ⟨1, ?_⟩⟩
  · rintro ⟨_, N, rfl⟩
    rw [hal, map_pow]
    exact hu.pow N
  · obtain ⟨N, a, ha⟩ := exists_mul_pow_eq_incl h c hc hg z
    exact ⟨(a, ⟨mon K c hc ^ N, N, rfl⟩), ha⟩
  · rw [incl_injective h hxy]

end GlobalTheory.CompanionTheory.SurjectionOntoH4.Away
