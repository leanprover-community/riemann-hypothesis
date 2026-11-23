module

import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.AdeleApproximation.AdeleIntA
public import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing
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
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.RingTheory.DedekindDomain.Factorization

@[expose] public section

noncomputable section

open IsDedekindDomain WithZero

namespace ReciprocityTheory.UG.AdeleIntA

variable {R K : Type*} [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K] [IsFractionRing R K]

def IsInt (y : FiniteAdeleRing R K) : Prop := ∀ v : HeightOneSpectrum R, y v ∈ v.adicCompletionIntegers K

theorem isInt_mul {x y : FiniteAdeleRing R K} (hx : IsInt x) (hy : IsInt y) : IsInt (x * y) :=
  fun v => mul_mem (hx v) (hy v)

theorem val_R (v : HeightOneSpectrum R) (r : R) :
    Valued.v (algebraMap K (v.adicCompletion K) (algebraMap R K r)) = v.intValuation r := by
  have h := v.valuedAdicCompletion_eq_valuation' (algebraMap R K r)
  rw [v.valuation_of_algebraMap] at h
  exact h

theorem isInt_R (r : R) : IsInt (algebraMap K (FiniteAdeleRing R K) (algebraMap R K r)) := by
  intro v
  rw [HeightOneSpectrum.mem_adicCompletionIntegers]
  show Valued.v (algebraMap K (v.adicCompletion K) (algebraMap R K r)) ≤ 1
  rw [val_R]
  exact v.intValuation_le_one r

theorem val_le_one_of_mem {v : HeightOneSpectrum R} {x : v.adicCompletion K} (h : x ∈ v.adicCompletionIntegers K) :
    Valued.v x ≤ 1 := (HeightOneSpectrum.mem_adicCompletionIntegers R K v).1 h

theorem local_approx (v : HeightOneSpectrum R) (x : v.adicCompletion K) (hx : Valued.v x ≤ 1) (m : R) (hm : m ≠ 0) :
    ∃ a : R, Valued.v (x - algebraMap K (v.adicCompletion K) (algebraMap R K a)) < v.intValuation m := by
  have hm0 : v.intValuation m ≠ 0 := v.intValuation_ne_zero m hm
  set γ : (ℤᵐ⁰)ˣ := Units.mk0 _ hm0
  set M : v.adicCompletion K := algebraMap K (v.adicCompletion K) (algebraMap R K m)
  have hM : Valued.v M = v.intValuation m := val_R v m
  have hMne : M ≠ 0 := fun h => hm0 (by rw [← hM, h, map_zero])
  have hM0 : (Valued.v : Valuation (v.adicCompletion K) ℤᵐ⁰).restrict M ≠ 0 := by
    simpa using hMne
  have hball : {z : v.adicCompletion K | Valued.v (z - x) < Valued.v M} ∈ nhds x :=
    (Valued.mem_nhds).2 ⟨Units.mk0 _ hM0, fun z hz => by
      simpa using (Valued.v : Valuation (v.adicCompletion K) ℤᵐ⁰).restrict_lt_iff.mp hz⟩
  obtain ⟨k, hk⟩ := (HeightOneSpectrum.denseRange_algebraMap (K := K) v).mem_nhds hball
  have hk' : Valued.v (algebraMap K (v.adicCompletion K) k - x) < v.intValuation m := hM ▸ hk
  have hk1 : v.valuation K k ≤ 1 := by
    rw [← HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
    have e : (k : v.adicCompletion K) = (algebraMap K (v.adicCompletion K) k - x) + x := by
      rw [sub_add_cancel]; rfl
    rw [e]
    refine (Valuation.map_add _ _ _).trans (max_le ?_ hx)
    exact hk'.le.trans (v.intValuation_le_one m)
  obtain ⟨a, ha⟩ := HeightOneSpectrum.exists_valuation_sub_lt_of_integer (K := K) v hk1 γ
  refine ⟨a, ?_⟩
  have e : x - algebraMap K (v.adicCompletion K) (algebraMap R K a) =
      -(algebraMap K (v.adicCompletion K) k - x) - algebraMap K (v.adicCompletion K) (algebraMap R K a - k) := by
    rw [map_sub]; ring
  rw [e]
  refine (Valuation.map_sub _ _ _).trans_lt (max_lt ?_ ?_)
  · rw [Valuation.map_neg]; exact hk'
  · have := HeightOneSpectrum.valuedAdicCompletion_eq_valuation' (v := v) (algebraMap R K a - k)
    change Valued.v (algebraMap K (v.adicCompletion K) (algebraMap R K a - k)) = _ at this
    rw [this]
    exact ha

theorem exists_approx (y : FiniteAdeleRing R K) (hy : ∀ v : HeightOneSpectrum R, y v ∈ v.adicCompletionIntegers K)
    (m : R) (hm : m ≠ 0) : ∃ a : R, ∀ v : HeightOneSpectrum R,
      Valued.v (y v - algebraMap K (v.adicCompletion K) (algebraMap R K a)) ≤ v.intValuation m := by
  classical
  have hfin : {v : HeightOneSpectrum R | v.asIdeal ∣ Ideal.span {m}}.Finite := by
    have hne : Ideal.span {m} ≠ ⊥ := by rwa [ne_eq, Ideal.span_singleton_eq_bot]
    have := Ideal.finite_factors hne
    exact this
  set S := hfin.toFinset
  choose b hb using fun v : HeightOneSpectrum R => local_approx v (y v) (val_le_one_of_mem (hy v)) m hm
  obtain ⟨a, ha⟩ := IsDedekindDomain.exists_forall_sub_mem_ideal (s := S) (fun v => v.asIdeal)
    (fun v => multiplicity v.asIdeal (Ideal.span {m})) (fun v _ => v.prime)
    (fun v _ w _ hvw h => hvw (HeightOneSpectrum.ext h)) (fun v => b v)
  refine ⟨a, fun v => ?_⟩
  have hloc := hb v
  by_cases hv : v ∈ S
  · have h1 := ha v hv
    rw [← HeightOneSpectrum.intValuation_le_pow_iff_mem, ← v.intValuation_eq_exp_neg_multiplicity hm] at h1
    have e : y v - algebraMap K (v.adicCompletion K) (algebraMap R K a) =
        (y v - algebraMap K (v.adicCompletion K) (algebraMap R K (b v))) -
          algebraMap K (v.adicCompletion K) (algebraMap R K (a - b v)) := by
      rw [map_sub, map_sub]; ring
    rw [e]
    refine (Valuation.map_sub _ _ _).trans (max_le hloc.le ?_)
    rw [val_R]
    exact h1
  · have hv1 : v.intValuation m = 1 := by
      rw [HeightOneSpectrum.intValuation_eq_one_iff_mem_primeCompl]
      intro hmem
      apply hv
      rw [Set.Finite.mem_toFinset]
      exact Ideal.dvd_iff_le.2 ((Ideal.span_singleton_le_iff_mem _).2 hmem)
    rw [hv1]
    refine (Valuation.map_sub _ _ _).trans (max_le (val_le_one_of_mem (hy v)) ?_)
    rw [val_R]
    exact v.intValuation_le_one a

theorem exists_approx_adele (α : FiniteAdeleRing R K) : ∃ u : K, IsInt (α - algebraMap K (FiniteAdeleRing R K) u) := by
  apply ReciprocityTheory.ChartRestriction.G.Lib.AdeleIntA.exists_approx_adele <;> assumption

end ReciprocityTheory.UG.AdeleIntA
