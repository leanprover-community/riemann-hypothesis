module

public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.RingTheory.PowerSeries.Basic
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.ResMapBijective
import Mathlib.Algebra.Module.StablyFree.Basic
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
import Mathlib.RingTheory.AdicCompletion.Noetherian
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Linter.Style
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
import Mathlib.Topology.Sheaves.Init
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.PairedDualFirstOrderDualMatrixSpace
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.RepAlg
public import Mathlib.LinearAlgebra.Dimension.Finite
public import Mathlib.LinearAlgebra.FreeModule.PID
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.PowerSeries.NoZeroDivisors

@[expose] public section

open Matrix IsLocalRing UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa

theorem UpperTheory.V.Pa.Det.extFree :
    ∀ {K K' : Type} [Field K] [Field K'] (j : PowerSeries K →+* PowerSeries K'), Function.Injective j → IsLocalHom j → j.Finite → ∃ (m : ℕ) (b : Fin m → PowerSeries K') (p : Fin m → PowerSeries K' →+ PowerSeries K), 0 < m ∧ (∀ y, y = ∑ i, j (p i y) * b i) ∧ (∀ i a y, p i (j a * y) = a * p i y) ∧ (∀ i i', p i (b i') = if i = i' then (1 : PowerSeries K) else 0) ∧ (∀ N : ℕ, ∃ N' : ℕ, ∀ y ∈ Ideal.span {(PowerSeries.X : PowerSeries K')} ^ N', ∀ i, p i y ∈ Ideal.span {(PowerSeries.X : PowerSeries K)} ^ N) ∧ ∃ (e : ℕ) (u : (PowerSeries K')ˣ), 0 < e ∧ j PowerSeries.X = (u : PowerSeries K') * (PowerSeries.X : PowerSeries K') ^ e := by
  intro K K' _ _ j hi hl hf
  letI : Algebra (PowerSeries K) (PowerSeries K') := j.toAlgebra
  haveI : Module.Finite (PowerSeries K) (PowerSeries K') := hf
  haveI : FaithfulSMul (PowerSeries K) (PowerSeries K') :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr hi
  haveI : Module.Free (PowerSeries K) (PowerSeries K') := Module.free_of_finite_type_torsion_free'
  let B := Module.finBasis (PowerSeries K) (PowerSeries K')
  have hsm : ∀ (a : PowerSeries K) (y : PowerSeries K'), j a * y = a • y := fun a y => rfl
  have hX : ∃ (e : ℕ) (u : (PowerSeries K')ˣ), 0 < e ∧
      j PowerSeries.X = (u : PowerSeries K') * (PowerSeries.X : PowerSeries K') ^ e := by
    have h0 : j PowerSeries.X ≠ 0 := by
      intro h
      exact PowerSeries.X_ne_zero (hi (h.trans (map_zero j).symm))
    obtain ⟨e, v, hv⟩ := IsDiscreteValuationRing.associated_pow_irreducible h0 (PowerSeries.X_irreducible (R := K'))
    refine ⟨e, v⁻¹, ?_, ?_⟩
    · rcases Nat.eq_zero_or_pos e with h | h
      · exfalso
        rw [h, pow_zero] at hv
        have hu : IsUnit (j PowerSeries.X) := IsUnit.of_mul_eq_one _ hv
        exact (PowerSeries.X_irreducible (R := K)).not_isUnit (isUnit_of_map_unit j _ hu)
      · exact h
    · rw [← hv, mul_left_comm, Units.inv_mul, mul_one]
  obtain ⟨e, u, he, hu⟩ := hX
  refine ⟨Module.finrank (PowerSeries K) (PowerSeries K'), fun i => B i, fun i => (B.coord i).toAddMonoidHom,
    Module.finrank_pos, ?_, ?_, ?_, ?_, e, u, he, hu⟩
  · intro y
    conv_lhs => rw [← B.sum_repr y]
    rfl
  · intro i a y
    show B.coord i (j a * y) = a * B.coord i y
    rw [hsm, LinearMap.map_smul, smul_eq_mul]
  · intro i i'
    show B.repr (B i') i = _
    rw [B.repr_self_apply]
    by_cases h : i = i'
    · subst h
      simp
    · simp [h, Ne.symm h]
  · intro N
    refine ⟨e * N, fun y hy i => ?_⟩
    rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton] at hy ⊢
    obtain ⟨z, rfl⟩ := hy
    have hu1 : (u : PowerSeries K') ^ N * ((u⁻¹ : (PowerSeries K')ˣ) : PowerSeries K') ^ N = 1 := by
      rw [← mul_pow, Units.mul_inv, one_pow]
    have hz : (PowerSeries.X : PowerSeries K') ^ (e * N) * z =
        j (PowerSeries.X ^ N) * (((u⁻¹ : (PowerSeries K')ˣ) : PowerSeries K') ^ N * z) := by
      rw [map_pow, hu, pow_mul]
      linear_combination (-(((PowerSeries.X : PowerSeries K') ^ e) ^ N * z)) * hu1
    refine ⟨B.coord i (((u⁻¹ : (PowerSeries K')ˣ) : PowerSeries K') ^ N * z), ?_⟩
    show B.coord i _ = _
    rw [hz, hsm, LinearMap.map_smul, smul_eq_mul]
