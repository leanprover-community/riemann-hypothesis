module

public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Completion
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
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRootSelectionUnitaryRankOne
import Development.AbelianVarietyTheory.Definitions.Divisors.IsCyclotomicExtensionQI
import Development.AbelianVarietyTheory.Definitions.Divisors.TwOrbMEqTwOrbUOfNormal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIntBTmulBasis

@[expose] public section

open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount IsDedekindDomain GlobalTheory.AdicSpan
open scoped TensorProduct Classical

namespace GlobalTheory

theorem adicCompletion_tensor_matrixUnit_identity : ∀ (L : Type) [Field L] [NumberField L] (C : Type) [Ring C] [Algebra ℚ C] (ι : L →ₐ[ℚ] C) (r : ℕ)
    (e : Fin r → C) (N : ℕ) (l : Fin N → L) (c : Fin N → C) (i i' : Fin r),
    (∀ β : Fin r → L, ∑ k, ι (l k) * (∑ i'', ι (β i'') * e i'') * c k = ι (β i') * e i) →
    ∀ (v : HeightOneSpectrum ℤ) (β : Fin r → v.adicCompletion ℚ ⊗[ℚ] L),
    ∑ k, Algebra.TensorProduct.map (AlgHom.id ℚ (v.adicCompletion ℚ)) ι ((1 : v.adicCompletion ℚ) ⊗ₜ[ℚ] l k) *
        (∑ i'', Algebra.TensorProduct.map (AlgHom.id ℚ (v.adicCompletion ℚ)) ι (β i'') *
          ((1 : v.adicCompletion ℚ) ⊗ₜ[ℚ] e i'')) * ((1 : v.adicCompletion ℚ) ⊗ₜ[ℚ] c k) =
      Algebra.TensorProduct.map (AlgHom.id ℚ (v.adicCompletion ℚ)) ι (β i') * ((1 : v.adicCompletion ℚ) ⊗ₜ[ℚ] e i) := by
  intro L _ _ C _ _ ι r e N l c i i' h v β
  set φ := Algebra.TensorProduct.map (AlgHom.id ℚ (v.adicCompletion ℚ)) ι with hφ
  let P : (Fin r → v.adicCompletion ℚ ⊗[ℚ] L) → Prop := fun β =>
    ∑ k, φ ((1 : v.adicCompletion ℚ) ⊗ₜ[ℚ] l k) *
        (∑ i'', φ (β i'') * ((1 : v.adicCompletion ℚ) ⊗ₜ[ℚ] e i'')) * ((1 : v.adicCompletion ℚ) ⊗ₜ[ℚ] c k) =
      φ (β i') * ((1 : v.adicCompletion ℚ) ⊗ₜ[ℚ] e i)
  have hzero : P 0 := by simp [P]
  have hadd : ∀ β₁ β₂, P β₁ → P β₂ → P (β₁ + β₂) := by
    intro β₁ β₂ h₁ h₂
    simp only [P, Pi.add_apply, map_add (f := _), add_mul, Finset.sum_add_distrib, mul_add] at h₁ h₂ ⊢
    rw [h₁, h₂]
  have hpure : ∀ (a : v.adicCompletion ℚ) (γ : Fin r → L), P (fun j => a ⊗ₜ[ℚ] γ j) := by
    intro a γ
    simp only [P, hφ, Algebra.TensorProduct.map_tmul, AlgHom.id_apply,
      Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul, ← TensorProduct.tmul_sum]
    rw [h γ]
  have hsingle : ∀ j x, P (Pi.single j x) := by
    intro j x
    induction x using TensorProduct.induction_on with
    | zero => simpa using hzero
    | tmul a m =>
      have : (Pi.single j (a ⊗ₜ[ℚ] m) : Fin r → v.adicCompletion ℚ ⊗[ℚ] L) =
          fun j' => a ⊗ₜ[ℚ] (Pi.single j m : Fin r → L) j' := by
        funext j'
        by_cases hj : j' = j
        · subst hj; simp
        · simp [Pi.single_apply, hj]
      rw [this]; exact hpure a _
    | add x y hx hy =>
      rw [Pi.single_add]; exact hadd _ _ hx hy
  have hall : P (∑ j, Pi.single j (β j)) :=
    Finset.sum_induction _ P hadd hzero (fun j _ => hsingle j (β j))
  rw [Finset.univ_sum_single] at hall
  exact hall

end GlobalTheory
