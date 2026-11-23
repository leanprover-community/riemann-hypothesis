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
import Mathlib.Tactic.Linter.Style
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

namespace GlobalTheory.ChartUnit

theorem isEval_comp {p : ℕ} {σ R A A' : Type} [CommRing R] [CommRing A] [CommRing A'] [Algebra R A] [Algebra R A']
    {x : σ → A} {E : MvPowerSeries σ R →ₐ[R] A} (φ : A →ₐ[R] A') (h : IsEval p x E) :
    IsEval p (fun i => φ (x i)) (φ.comp E) := by
  refine ⟨fun i => by simp [h.1 i], fun m => ?_⟩
  obtain ⟨N, hN⟩ := h.2 m
  refine ⟨N, fun f hf => ?_⟩
  have := map_dvd φ (hN f hf)
  simpa using this

theorem lift_counit_eq {O A : Type} [CommRing O] [CommRing A] [Bialgebra O A] (t : A ⊗[O] A) :
    Algebra.TensorProduct.lift (AlgHom.id O A) ((Algebra.ofId O A).comp (Bialgebra.counitAlgHom O A))
      (fun _ _ => Commute.all _ _) t = TensorProduct.rid O A (LinearMap.lTensor A (Coalgebra.counit (R := O)) t) := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul a b => simp [Algebra.smul_def, mul_comm]
  | add s t hs ht => simp only [map_add (f := _), hs, ht]

end GlobalTheory.ChartUnit


open GlobalTheory.ChartUnit in
theorem GlobalTheory.chart_unit : ∀ (p : ℕ) (O A : Type) [CommRing O] [CommRing A] [Bialgebra O A] [IsAdicComplete (Ideal.span {(p : A)}) A] {d : ℕ} (x : Fin d → A) (ev : MvPowerSeries (Fin d) O →ₐ[O] A) (E₂ : MvPowerSeries (Fin d ⊕ Fin d) O →ₐ[O] A ⊗[O] A) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) O), (∀ i, ∃ N : ℕ, (p : A) ∣ x i ^ N) → (∀ i, Coalgebra.counit (R := O) (x i) = 0) → IsEval p x ev → IsEval p (Sum.elim (fun i => x i ⊗ₜ[O] (1 : A)) fun i => (1 : A) ⊗ₜ[O] x i) E₂ → (∀ i, E₂ (μ i) = Coalgebra.comul (R := O) (x i)) → ∀ i, ev (op μ (fun i => (X i : MvPowerSeries (Fin d) O)) (fun _ => 0) i) = x i := by
  intro p O A _ _ _ _ d x ev E₂ μ hnil hcu hev hev₂ hcomul i
  set ψ : A ⊗[O] A →ₐ[O] A := Algebra.TensorProduct.lift (AlgHom.id O A)
    ((Algebra.ofId O A).comp (Bialgebra.counitAlgHom O A)) (fun _ _ => Commute.all _ _) with hψ
  have key := (GlobalTheory.CEval.continuous_eval p O A (Fin d) x hnil).2 ev hev
  let u : Fin d ⊕ Fin d → MvPowerSeries (Fin d) O :=
    Sum.elim (fun i => (X i : MvPowerSeries (Fin d) O)) (fun _ => 0)
  have hE' : IsEval p (fun j => ev (u j)) (ψ.comp E₂) := by
    have h := isEval_comp ψ hev₂
    convert h using 2 with j
    rcases j with j | j
    · simp [u, hψ, hev.1 j]
    · simp [u, hψ, hcu j]
  have hu : ∀ j, constantCoeff (u j) = 0 := by
    intro j; rcases j with j | j <;> simp [u]
  have := key.1 (Fin d ⊕ Fin d) u (ψ.comp E₂) hu hE' (μ i)
  show ev (subst u (μ i)) = x i
  rw [this, AlgHom.comp_apply, hcomul, hψ, lift_counit_eq, Coalgebra.lTensor_counit_comul]
  simp
