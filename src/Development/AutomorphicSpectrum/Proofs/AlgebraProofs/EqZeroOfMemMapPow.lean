module

public import Mathlib.Algebra.MonoidAlgebra.Basic
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
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
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
public import Mathlib.RingTheory.Filtration

@[expose] public section

open Matrix Filter Topology
open scoped BigOperators ComplexOrder

namespace GlobalTheory.CompanionTheory.KrullGroupAlg

theorem coeff_mem_of_mem_map {R M : Type} [CommRing R] [AddCommGroup M] (I : Ideal R)
    (x : AddMonoidAlgebra R M) (hx : x ∈ Ideal.map (algebraMap R (AddMonoidAlgebra R M)) I)
    (φ : AddMonoidAlgebra R M →ₗ[R] R) : φ x ∈ I := by
  have hx' : x ∈ Submodule.span (AddMonoidAlgebra R M) (algebraMap R (AddMonoidAlgebra R M) '' I) := hx
  clear hx
  revert φ
  induction hx' using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨a, ha, rfl⟩ := hy
    intro φ
    rw [Algebra.algebraMap_eq_smul_one, map_smul, smul_eq_mul]
    exact I.mul_mem_right _ ha
  | zero =>
    intro φ
    rw [map_zero]
    exact I.zero_mem
  | add y z _ _ hy hz =>
    intro φ
    rw [map_add (f := _)]
    exact I.add_mem (hy φ) (hz φ)
  | smul r y _ hy =>
    intro φ
    have := hy (φ ∘ₗ LinearMap.mulLeft R r)
    simpa [smul_eq_mul] using this

theorem eq_zero_of_mem_map_pow : ∀ (R M : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [AddCommGroup M] (x : AddMonoidAlgebra R M), (∀ n : ℕ, x ∈ Ideal.map (algebraMap R (AddMonoidAlgebra R M)) (IsLocalRing.maximalIdeal R ^ n)) → x = 0 := by
  intro R M _ _ _ _ x hx
  ext m
  have hm : (Finsupp.lapply m ∘ₗ (AddMonoidAlgebra.coeffLinearEquiv R).toLinearMap) x ∈ ⨅ n : ℕ, IsLocalRing.maximalIdeal R ^ n :=
    Ideal.mem_iInf.2 fun n =>
      coeff_mem_of_mem_map _ x (hx n) (Finsupp.lapply m ∘ₗ (AddMonoidAlgebra.coeffLinearEquiv R).toLinearMap)
  rw [Ideal.iInf_pow_eq_bot_of_isLocalRing _ (IsLocalRing.maximalIdeal.isMaximal R).ne_top,
    Ideal.mem_bot] at hm
  simpa using hm

end GlobalTheory.CompanionTheory.KrullGroupAlg
