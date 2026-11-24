module

public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StIsolatedPointsCountPrime
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
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.RingTheory.Ideal.MinimalPrime.Noetherian

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial Topology ComplexSets

noncomputable section

theorem exists_minimalPrime_mem_zeroSet {n : ℕ} (J : Ideal (MvPolynomial (Fin n) ℂ)) {x : Fin n → ℂ}
    (hx : x ∈ zeroSet J) : ∃ P ∈ J.minimalPrimes, x ∈ zeroSet P := by
  have hJ : J ≤ RingHom.ker (eval x) := fun q hq => (RingHom.mem_ker).2 (hx q hq)
  have : (RingHom.ker (eval x : MvPolynomial (Fin n) ℂ →+* ℂ)).IsPrime := RingHom.ker_isPrime _
  obtain ⟨P, hP, hPle⟩ := Ideal.exists_minimalPrimes_le hJ
  exact ⟨P, hP, fun q hq => (RingHom.mem_ker).1 (hPle hq)⟩

theorem mem_isolatedFibrePts_of_le {n m : ℕ} {J P : Ideal (MvPolynomial (Fin n) ℂ)} (hJP : J ≤ P)
    (Q : Fin m → MvPolynomial (Fin n) ℂ) (z : Fin m → ℂ) {x : Fin n → ℂ}
    (hx : x ∈ isolatedFibrePts J Q z) (hxP : x ∈ zeroSet P) : x ∈ isolatedFibrePts P Q z := by
  obtain ⟨-, hQ, V, hV, hiso⟩ := hx
  exact ⟨hxP, hQ, V, hV, fun x' hx' hQ' => hiso x' ⟨fun q hq => hx'.1 q (hJP hq), hx'.2⟩ hQ'⟩

theorem encard_biUnion_finset_le {ι α : Type*} (S : Finset ι) (f : ι → Set α) :
    (⋃ i ∈ S, f i).encard ≤ ∑ i ∈ S, (f i).encard := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | insert a S ha ih =>
    rw [Finset.sum_insert ha, Finset.set_biUnion_insert]
    exact (Set.encard_union_le _ _).trans (add_le_add_right ih _)

theorem IsolatedPointsCount.proof (hPrime : IsolatedPointsCountPrime.Statement) :
    IsolatedPointsCount.Statement := by
  classical
  intro n m J Q
  have hfin := Ideal.finite_minimalPrimes_of_isNoetherianRing (MvPolynomial (Fin n) ℂ) J
  have hN : ∀ P ∈ J.minimalPrimes, ∃ N : ℕ, ∀ z : Fin m → ℂ, (isolatedFibrePts P Q z).encard ≤ N :=
    fun P hP => hPrime n m P hP.1.1 Q
  choose! N hN using hN
  refine ⟨∑ P ∈ hfin.toFinset, N P, fun z => ?_⟩
  have hsub : isolatedFibrePts J Q z ⊆ ⋃ P ∈ hfin.toFinset, isolatedFibrePts P Q z := by
    intro x hx
    obtain ⟨P, hP, hxP⟩ := exists_minimalPrime_mem_zeroSet J hx.1
    exact Set.mem_biUnion (hfin.mem_toFinset.2 hP) (mem_isolatedFibrePts_of_le hP.1.2 Q z hx hxP)
  calc (isolatedFibrePts J Q z).encard
      ≤ (⋃ P ∈ hfin.toFinset, isolatedFibrePts P Q z).encard := Set.encard_le_encard hsub
    _ ≤ ∑ P ∈ hfin.toFinset, (isolatedFibrePts P Q z).encard := encard_biUnion_finset_le _ _
    _ ≤ ∑ P ∈ hfin.toFinset, ((N P : ℕ) : ℕ∞) :=
        Finset.sum_le_sum fun P hP => hN P (hfin.mem_toFinset.1 hP) z
    _ = ((∑ P ∈ hfin.toFinset, N P : ℕ) : ℕ∞) := by push_cast; rfl

end

end GroundTheory.Heights₂.Heights
