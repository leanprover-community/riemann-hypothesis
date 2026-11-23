module

public import Development.AbelianVarietyTheory.Definitions.Jets.CmLatticeCommutatorPairingPowEqOneOfGoodLift
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
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

open PowerSeries GlobalTheory.MomOne
open scoped ComplexConjugate BigOperators Topology

namespace GlobalTheory.MomOne

theorem norm_sum_prod_le_of_coord {K : Type*} [NormedCommRing K] {g m : ℕ} (F G : Fin m → Fin g → ℕ → K)
    (c : Fin m → K) (B : ℝ)
    (step : ∀ (i : Fin g) (c' : Fin m → K), (∀ n, ‖∑ j, c' j * F j i n‖ ≤ B) → ∀ n, ‖∑ j, c' j * G j i n‖ ≤ B)
    (h : ∀ ν : Fin g → ℕ, ‖∑ j, c j * ∏ i, F j i (ν i)‖ ≤ B) (ν : Fin g → ℕ) :
    ‖∑ j, c j * ∏ i, G j i (ν i)‖ ≤ B := by
  classical
  have key : ∀ I : Finset (Fin g), ∀ ν : Fin g → ℕ,
      ‖∑ j, c j * ∏ i, (if i ∈ I then G j i (ν i) else F j i (ν i))‖ ≤ B := by
    intro I
    induction I using Finset.induction_on with
    | empty => simpa using h
    | insert i₀ I hi ih =>
      intro ν
      have hs := step i₀
        (fun j => c j * ∏ i ∈ Finset.univ.erase i₀, (if i ∈ I then G j i (ν i) else F j i (ν i))) ?_ (ν i₀)
      · convert hs using 3 with j _
        rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ i₀), mul_assoc]
        congr 2
        · refine Finset.prod_congr rfl fun i hi' => ?_
          simp [Finset.mem_insert, Finset.ne_of_mem_erase hi']
        · simp
      · intro n
        convert ih (Function.update ν i₀ n) using 3 with j _
        rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ i₀), mul_assoc]
        congr 2
        · refine Finset.prod_congr rfl fun i hi' => ?_
          simp [Function.update_of_ne (Finset.ne_of_mem_erase hi')]
        · simp [hi]
  simpa using key Finset.univ ν

theorem translate_norm_prod_le : ∀ (d q : ℕ) [Fact q.Prime] (ι : ℂ ≃+* ℂ_[q]) (ω : ℂ_[q]) (θ : ℂ → ℂ), ThetaLaws ι d ω θ → ∀ (g m : ℕ) (a : Fin g → ℕ) (c : Fin m → ℂ_[q]) (t : Fin m → Fin g → ℂ) (τ : Fin g → ℂ) (B : ℝ), (∀ j i, PrimeTo d q (t j i)) → (∀ i, PrimeTo d q (τ i)) → (∀ ν : Fin g → ℕ, ‖∑ j, c j * ∏ i, coeff (ν i) (hat ι (C ω * logS) (U1 d (t j i) θ) ^ a i)‖ ≤ B) → ∀ ν : Fin g → ℕ, ‖∑ j, c j * ∏ i, coeff (ν i) (hat ι (C ω * logS) (U1 d (τ i) (U1 d (t j i) θ)) ^ a i)‖ ≤ B := by
  intro d q _ ι ω θ hθ g m a c t τ B ht hτ h
  refine norm_sum_prod_le_of_coord
    (fun j i n => coeff n (hat ι (C ω * logS) (U1 d (t j i) θ) ^ a i))
    (fun j i n => coeff n (hat ι (C ω * logS) (U1 d (τ i) (U1 d (t j i) θ)) ^ a i)) c B ?_ h
  intro i c' hc n
  have := hθ.2.2 (a i) m c' (fun j => t j i) (τ i) B (fun j => ht j i) (hτ i) (fun k => by

    simpa only [map_sum, coeff_C_mul] using hc k) n

  simpa only [map_sum, coeff_C_mul] using this

end GlobalTheory.MomOne
