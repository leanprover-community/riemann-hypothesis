module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalMaximality.ResidueOfTraceIsFiberSum
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
public import Mathlib.RingTheory.Trace.Basic

@[expose] public section

open KaehlerDifferential GlobalTheory.CechDR GlobalTheory.PD GlobalTheory.WH GlobalTheory.W1 UpperTheory.Gal.productCup_of_system
open scoped TensorProduct

section
variable {F K K' : Type} [Field F] [Field K] [Field K'] [Algebra ℂ F] [Algebra ℂ K] [Algebra ℂ K'] [Algebra F K]
  [IsScalarTower ℂ F K] [Algebra K K'] [IsScalarTower ℂ K K'] [Algebra F K'] [IsScalarTower F K K']
  [IsScalarTower ℂ F K'] {d : ℕ}

private theorem tower_rA (y : Fin (d + 1) → F) : IsScalarTower (rA ℂ y {0}) K K' :=
  .of_algebraMap_eq fun r => IsScalarTower.algebraMap_apply F K K' (r : F)

private theorem map_mem_rB (y : Fin (d + 1) → F) {b : K} (hb : b ∈ rB ℂ K y {0}) :
    algebraMap K K' b ∈ rB ℂ K' y {0} := by
  rw [rB, Subalgebra.mem_restrictScalars, mem_integralClosure_iff] at hb ⊢
  haveI := tower_rA (K := K) (K' := K') y
  exact hb.algebraMap

private theorem trace_mem_rB (y : Fin (d + 1) → F) [FiniteDimensional K K'] {v : K'}
    (hv : v ∈ rB ℂ K' y {0}) : Algebra.trace K K' v ∈ rB ℂ K y {0} := by
  rw [rB, Subalgebra.mem_restrictScalars, mem_integralClosure_iff] at hv ⊢
  haveI := tower_rA (K := K) (K' := K') y
  exact Algebra.isIntegral_trace hv

end

theorem UpperTheory.Gal.productCup_of_system.redK_of :
    RedK := by
  intro F K K' _ _ _ _ _ _ _ _ _ _ _ _ _ d x j2 hY
  haveI : FiniteDimensional F K' := hY.covY.fin
  haveI : FiniteDimensional K K' := Module.Finite.of_restrictScalars_finite F K K'
  have hred := hY.red
  unfold RedFib at hred ⊢
  constructor
  intro z hz
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective z
  obtain ⟨n, hn⟩ := hz
  rw [← map_pow, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_range_iff_exists_fun] at hn
  obtain ⟨c, hc⟩ := hn
  rw [Ideal.Quotient.eq_zero_iff_mem]
  set t : Fin d → F := fun j => xv x j.succ / xv x 0 with ht
  have hcK : ∑ j, (c j : K) * algebraMap F K (t j) = (a : K) ^ n := by
    have := congrArg (fun u : rB ℂ K (xv x) {0} => (u : K)) hc
    simpa only [AddSubmonoidClass.coe_finsetSum, MulMemClass.coe_mul, SubmonoidClass.coe_pow] using this
  let b : rB ℂ K' (xv x) {0} := ⟨algebraMap K K' a, map_mem_rB (xv x) a.2⟩
  have hb : b ∈ Ideal.span (Set.range fun j : Fin d =>
      (⟨algebraMap F K' (t j), tco_mem ℂ K' (xv x) j⟩ : rB ℂ K' (xv x) {0})) := by
    have hq : IsNilpotent (Ideal.Quotient.mk (Ideal.span (Set.range fun j : Fin d =>
        (⟨algebraMap F K' (t j), tco_mem ℂ K' (xv x) j⟩ : rB ℂ K' (xv x) {0}))) b) := by
      refine ⟨n, ?_⟩
      rw [← map_pow, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_range_iff_exists_fun]
      refine ⟨fun j => ⟨algebraMap K K' (c j), map_mem_rB (xv x) (c j).2⟩, ?_⟩
      apply Subtype.ext
      simp only [b, AddSubmonoidClass.coe_finsetSum, MulMemClass.coe_mul, SubmonoidClass.coe_pow]

      rw [← map_pow, ← hcK, map_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [map_mul, ← IsScalarTower.algebraMap_apply]
    exact (Ideal.Quotient.eq_zero_iff_mem).1 (hred.eq_zero _ hq)
  rw [Ideal.mem_span_range_iff_exists_fun] at hb
  obtain ⟨e, he⟩ := hb
  have key : (Module.finrank K K' : K) * (a : K) =
      ∑ j, Algebra.trace K K' (e j : K') * algebraMap F K (t j) := by
    have h1 := congrArg (fun u : rB ℂ K' (xv x) {0} => Algebra.trace K K' (u : K')) he

    simp only [b, AddSubmonoidClass.coe_finsetSum, MulMemClass.coe_mul, map_sum,
    Algebra.trace_algebraMap, nsmul_eq_mul] at h1
    rw [← h1]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [IsScalarTower.algebraMap_apply F K K', mul_comm, ← Algebra.smul_def, map_smul, smul_eq_mul,
      mul_comm]
  have hmem : ((Module.finrank K K' : rB ℂ K (xv x) {0}) * a) ∈ Ideal.span (Set.range fun j : Fin d =>
      (⟨algebraMap F K (t j), tco_mem ℂ K (xv x) j⟩ : rB ℂ K (xv x) {0})) := by
    rw [Ideal.mem_span_range_iff_exists_fun]
    refine ⟨fun j => ⟨Algebra.trace K K' (e j : K'), trace_mem_rB (xv x) (e j).2⟩, ?_⟩
    apply Subtype.ext
    simp only [AddSubmonoidClass.coe_finsetSum, MulMemClass.coe_mul, SubringClass.coe_natCast]
    exact key.symm
  have hpos : (Module.finrank K K' : ℂ) ≠ 0 := by
    exact_mod_cast (Module.finrank_pos (R := K) (M := K')).ne'
  have hA : a = algebraMap ℂ (rB ℂ K (xv x) {0}) ((Module.finrank K K' : ℂ)⁻¹) *
      ((Module.finrank K K' : rB ℂ K (xv x) {0}) * a) := by
    rw [← mul_assoc, ← map_natCast (algebraMap ℂ (rB ℂ K (xv x) {0})), ← map_mul,
      inv_mul_cancel₀ hpos, map_one, one_mul]
  rw [hA]
  exact Ideal.mul_mem_left _ _ hmem
