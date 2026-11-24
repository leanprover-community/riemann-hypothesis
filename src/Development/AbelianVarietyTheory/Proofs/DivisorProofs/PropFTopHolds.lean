module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LaurentMapIsIntegral
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

@[expose] public section

open GlobalTheory.EtC.GmStep

namespace GlobalTheory.EtC.GmStep

theorem laurentPi_bijective : ∀ (n : ℕ) (B : Fin n → Type) [∀ j, CommRing (B j)], Function.Bijective (Pi.ringHom (fun j => laurentMap (Pi.evalRingHom B j)) : LaurentPolynomial (∀ j, B j) →+* ∀ j, LaurentPolynomial (B j)) := by
  intro n B _
  have hap : ∀ (x : LaurentPolynomial (∀ j, B j)) k, (Pi.ringHom (fun j => laurentMap (Pi.evalRingHom B j)) : LaurentPolynomial (∀ j, B j) →+* ∀ j, LaurentPolynomial (B j)) x k = laurentMap (Pi.evalRingHom B k) x := fun _ _ => rfl
  constructor
  · rw [injective_iff_map_eq_zero]
    intro p hp
    have hc : p.coeff = 0 := by
      ext m j
      have h1 := congrArg (fun r : ∀ j, LaurentPolynomial (B j) => (r j).coeff m) hp
      simp only [hap, Pi.zero_apply, laurentMap_coeff, Finsupp.mapRange_apply] at h1
      simpa using h1
    exact AddMonoidAlgebra.ext hc
  · intro F
    have hsub : ∀ j (q : LaurentPolynomial (B j)), Pi.single j q ∈ (Pi.ringHom (fun j => laurentMap (Pi.evalRingHom B j)) : LaurentPolynomial (∀ j, B j) →+* ∀ j, LaurentPolynomial (B j)).range := by
      intro j q
      induction q using LaurentPolynomial.induction_on' with
      | add p r hp hr =>
        rw [Pi.single_add]; exact Subring.add_mem _ hp hr
      | C_mul_T m a =>
        refine ⟨LaurentPolynomial.C (Pi.single j a) * LaurentPolynomial.T m, ?_⟩
        funext k
        simp only [hap, map_mul, laurentMap_C, laurentMap_T, Pi.evalRingHom_apply]
        by_cases hk : k = j
        · subst hk; simp
        · simp [Pi.single_eq_of_ne hk]
    rw [← Finset.univ_sum_single F]
    obtain ⟨p, hp⟩ := Subring.sum_mem _ (fun j (_ : j ∈ Finset.univ) => hsub j (F j))
    exact ⟨p, hp⟩

end GlobalTheory.EtC.GmStep
