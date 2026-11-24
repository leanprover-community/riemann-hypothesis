module

public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ExistsValuationSubLeOne
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

namespace GroundTheory.Global

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
open scoped RestrictedProduct

variable {R : Type*} [CommRing R] [IsDedekindDomain R] {K : Type*} [Field K] [Algebra R K]
  [IsFractionRing R K]

def integralFiniteAdeles (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K]
    [IsFractionRing R K] : Subring (FiniteAdeleRing R K) where
  carrier := {a | ∀ v : HeightOneSpectrum R, a v ∈ v.adicCompletionIntegers K}
  mul_mem' ha hb v := Subring.mul_mem _ (ha v) (hb v)
  one_mem' _ := Subring.one_mem _
  add_mem' ha hb v := Subring.add_mem _ (ha v) (hb v)
  zero_mem' _ := Subring.zero_mem _
  neg_mem' ha v := Subring.neg_mem _ (ha v)

theorem mem_integralFiniteAdeles {a : FiniteAdeleRing R K} :
    a ∈ integralFiniteAdeles R K ↔ ∀ v : HeightOneSpectrum R, a v ∈ v.adicCompletionIntegers K :=
  Iff.rfl

theorem isOpen_integralFiniteAdeles :
    IsOpen (integralFiniteAdeles R K : Set (FiniteAdeleRing R K)) :=
  RestrictedProduct.isOpen_forall_mem (R := fun v : HeightOneSpectrum R => v.adicCompletion K)
    (A := fun v => (v.adicCompletionIntegers K : Set (v.adicCompletion K)))
    (fun _ => Valued.isOpen_valuationSubring _)

theorem coe_mem_adicCompletionIntegers_iff (v : HeightOneSpectrum R) (k : K) :
    (k : v.adicCompletion K) ∈ v.adicCompletionIntegers K ↔ v.valuation K k ≤ 1 := by
  rw [mem_adicCompletionIntegers, valuedAdicCompletion_eq_valuation']

theorem exists_sub_mem_integralFiniteAdeles (a : FiniteAdeleRing R K) :
    ∃ k : K, a - algebraMap K (FiniteAdeleRing R K) k ∈ integralFiniteAdeles R K := by
  classical
  have hS : {v : HeightOneSpectrum R | a v ∉ v.adicCompletionIntegers K}.Finite :=
    Filter.eventually_cofinite.mp a.2
  have hx : ∀ v : HeightOneSpectrum R, ∃ z : K,
      a v - (z : v.adicCompletion K) ∈ v.adicCompletionIntegers K := by
    intro v
    have hU : IsOpen {w : v.adicCompletion K | a v - w ∈ v.adicCompletionIntegers K} :=
      (Valued.isOpen_valuationSubring (v.adicCompletion K)).preimage
        (continuous_const.sub continuous_id)
    obtain ⟨z, hz⟩ := (denseRange_algebraMap (K := K) v).exists_mem_open hU
      ⟨a v, by simp⟩
    exact ⟨z, hz⟩
  choose x hx using hx
  obtain ⟨k, hkS, hkn⟩ := _root_.UpperTheory.Reformulated.B.ExistsValuationSubLeOne.exists_valuation_sub_le_one hS.toFinset x
  refine ⟨k, fun v => ?_⟩
  change a v - (k : v.adicCompletion K) ∈ v.adicCompletionIntegers K
  by_cases hv : v ∈ hS.toFinset
  · have h1 := (coe_mem_adicCompletionIntegers_iff v (k - x v)).mpr (hkS v hv)
    have h2 : a v - (k : v.adicCompletion K) =
        (a v - (x v : v.adicCompletion K)) - ((k - x v : K) : v.adicCompletion K) := by
      have hc : ∀ z : K, (z : v.adicCompletion K) = algebraMap K (v.adicCompletion K) z :=
        fun z => by simp [algebraMap_adicCompletion]
      rw [hc, hc, hc, map_sub]
      ring
    rw [h2]
    exact Subring.sub_mem _ (hx v) h1
  · have hav : a v ∈ v.adicCompletionIntegers K := by
      simpa using hv
    exact Subring.sub_mem _ hav ((coe_mem_adicCompletionIntegers_iff v k).mpr (hkn v hv))

instance : T2Space (FiniteAdeleRing R K) :=
  inferInstanceAs (T2Space
    (Πʳ v : HeightOneSpectrum R, [v.adicCompletion K, v.adicCompletionIntegers K]))

instance (F : Type*) [Field F] : T2Space (NumberField.InfiniteAdeleRing F) :=
  inferInstanceAs (T2Space ((v : NumberField.InfinitePlace F) → v.Completion))

instance : T2Space (NumberField.AdeleRing R K) :=
  inferInstanceAs (T2Space (NumberField.InfiniteAdeleRing K × FiniteAdeleRing R K))

end GroundTheory.Global
