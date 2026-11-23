module

public import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PadicContinuousEvaluationExistsUniqueSubstNatura
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.EpsilonPairingZeta
import Development.AbelianVarietyTheory.Definitions.Divisors.GhostFrobenius

@[expose] public section

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat
open TensorProduct

namespace GlobalTheory.CommSwap

theorem eval_swap_eq : ∀ (p : ℕ) (O A : Type) [CommRing O] [CommRing A] [Bialgebra O A] [Coalgebra.IsCocomm O A] [IsAdicComplete (Ideal.span {(p : A ⊗[O] A)}) (A ⊗[O] A)] {d : ℕ} (x : Fin d → A) (E₂ : MvPowerSeries (Fin d ⊕ Fin d) O →ₐ[O] A ⊗[O] A) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) O), (∀ i, ∃ N : ℕ, (p : A) ∣ x i ^ N) → IsEval p (Sum.elim (fun i => x i ⊗ₜ[O] (1 : A)) fun i => (1 : A) ⊗ₜ[O] x i) E₂ → (∀ i, E₂ (μ i) = Coalgebra.comul (R := O) (x i)) → ∀ i, E₂ (swap (μ i)) = E₂ (μ i) := by
  intro p O A _ _ _ _ _ d x E₂ μ hnil hE hμ i
  set y : Fin d ⊕ Fin d → A ⊗[O] A := Sum.elim (fun i => x i ⊗ₜ[O] (1 : A)) fun i => (1 : A) ⊗ₜ[O] x i with hy
  have hny : ∀ j, ∃ N : ℕ, (p : A ⊗[O] A) ∣ y j ^ N := by
    intro j
    rcases j with j | j
    · obtain ⟨N, a, ha⟩ := hnil j
      refine ⟨N, a ⊗ₜ[O] 1, ?_⟩
      have h1 := map_mul (Algebra.TensorProduct.includeLeftRingHom (R := O) (A := A) (B := A)) (p : A) a
      simp only [Algebra.TensorProduct.includeLeftRingHom_apply, map_natCast] at h1
      simp only [hy, Sum.elim_inl, Algebra.TensorProduct.tmul_pow, one_pow, ha, h1]
    · obtain ⟨N, a, ha⟩ := hnil j
      refine ⟨N, 1 ⊗ₜ[O] a, ?_⟩
      have h1 := map_mul (Algebra.TensorProduct.includeRight (R := O) (A := A) (B := A)) (p : A) a
      simp only [Algebra.TensorProduct.includeRight_apply, map_natCast] at h1
      simp only [hy, Sum.elim_inr, Algebra.TensorProduct.tmul_pow, one_pow, ha, h1]
  set T := (Algebra.TensorProduct.comm O A A).toAlgHom
  set E' := T.comp E₂
  set u : Fin d ⊕ Fin d → MvPowerSeries (Fin d ⊕ Fin d) O :=
    Sum.elim (fun i => X (Sum.inr i)) (fun i => X (Sum.inl i)) with hu
  have hu0 : ∀ j, constantCoeff (u j) = 0 := by
    intro j; rcases j with j | j <;> simp [hu]
  have hE' : IsEval p (fun j => E₂ (u j)) E' := by
    refine ⟨?_, ?_⟩
    · intro j
      rcases j with j | j
      · simp [E', T, hu, hE.1, hy]
      · simp [E', T, hu, hE.1, hy]
    · intro m
      obtain ⟨N, hN⟩ := hE.2 m
      refine ⟨N, fun f hf => ?_⟩
      obtain ⟨c, hc⟩ := hN f hf
      refine ⟨T c, ?_⟩
      simp [E', hc, map_mul, map_pow, map_natCast]
  have key := ((GlobalTheory.CEval.continuous_eval p O (A ⊗[O] A) (Fin d ⊕ Fin d) y hny).2 E₂ hE).1 (Fin d ⊕ Fin d) u E' hu0 hE' (μ i)
  have hs : swap (μ i) = subst u (μ i) := rfl
  rw [hs, key, hμ i]
  simp only [E', T, AlgHom.comp_apply, hμ i]
  exact Coalgebra.comm_comul (R := O) (x i)

end GlobalTheory.CommSwap
