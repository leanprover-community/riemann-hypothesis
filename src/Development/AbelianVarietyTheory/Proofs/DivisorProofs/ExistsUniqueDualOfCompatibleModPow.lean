module

public import Mathlib.LinearAlgebra.Dual.Defs
public import Mathlib.RingTheory.AdicCompletion.Basic
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
import Development.AbelianVarietyTheory.Definitions.Divisors.FormalCoboundarySmul
import Development.AbelianVarietyTheory.Definitions.Divisors.KerIdealCompOfSurjective
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsCounitDerivationCounitComp
import Mathlib.RingTheory.MvPowerSeries.Basic

@[expose] public section

open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup

namespace GlobalTheory.PDiv

theorem exists_unique_dual_of_compatible_mod_pow :
    ∀ (O M : Type) [CommRing O] [AddCommGroup M] [Module O M] (a : O)
      [IsAdicComplete (Ideal.span {a}) O] (u : ∀ n : ℕ, M →ₗ[O] O ⧸ Ideal.span {a ^ n}),
      (∀ n w (x : O), u (n + 1) w = Ideal.Quotient.mk _ x → u n w = Ideal.Quotient.mk _ x) →
      ∃! l : Module.Dual O M, ∀ n w, Ideal.Quotient.mk _ (l w) = u n w := by
  intro O M _ _ _ a _ u hu

  have sep : ∀ y : O, (∀ n : ℕ, y ∈ Ideal.span {a ^ n}) → y = 0 := by
    intro y hy
    refine IsHausdorff.haus' (I := Ideal.span {a}) y fun n => ?_
    rw [SModEq.zero, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow]
    exact hy n
  have key : ∀ w : M, ∃! y : O, ∀ n, Ideal.Quotient.mk (Ideal.span {a ^ n}) y = u n w := by
    intro w
    choose x hx using fun n => Ideal.Quotient.mk_surjective (u n w)
    have step : ∀ n, x n - x (n + 1) ∈ Ideal.span {a ^ n} := by
      intro n
      exact Ideal.Quotient.eq.mp ((hx n).trans (hu n w (x (n + 1)) (hx (n + 1)).symm))
    have cauchy : ∀ m n, m ≤ n → x m - x n ∈ Ideal.span {a ^ m} := by
      intro m n hmn
      induction n, hmn using Nat.le_induction with
      | base => simp
      | succ k hmk ih =>
        have h2 : x k - x (k + 1) ∈ Ideal.span {a ^ m} :=
          (Ideal.span_singleton_le_span_singleton.mpr (pow_dvd_pow a hmk)) (step k)
        have := Ideal.add_mem _ ih h2
        simpa using this
    obtain ⟨L, hL⟩ := IsPrecomplete.prec' (I := Ideal.span {a}) x (fun {m n} hmn => by
      rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow]
      exact cauchy m n hmn)
    refine ⟨L, fun n => ?_, fun y hy => ?_⟩
    · have h := hL n
      rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow] at h
      rw [← hx n]
      exact Ideal.Quotient.eq.mpr (by simpa using (Ideal.span {a ^ n}).neg_mem h)
    · refine sub_eq_zero.mp (sep _ fun n => ?_)
      have h := hL n
      rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow] at h
      exact Ideal.Quotient.eq.mp ((hy n).trans (hx n).symm) |> fun h' => by
        simpa using Ideal.add_mem _ h' h
  choose f hf huniq using key
  refine ⟨{ toFun := f, map_add' := ?_, map_smul' := ?_ }, ?_, ?_⟩
  · intro w w'
    refine (huniq (w + w') _ fun n => ?_).symm
    rw [map_add (f := _), map_add (f := _), hf, hf]
  · intro c w
    refine (huniq (c • w) _ fun n => ?_).symm
    rw [RingHom.id_apply, smul_eq_mul, map_mul, map_smul, ← hf w n, Algebra.smul_def,
      Ideal.Quotient.algebraMap_eq]
  · exact fun n w => hf w n
  · intro l hl
    exact LinearMap.ext fun w => huniq w (l w) fun n => hl n w

end GlobalTheory.PDiv
