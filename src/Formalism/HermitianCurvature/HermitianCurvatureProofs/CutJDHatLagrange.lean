module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJDHat
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.IsAdmissibleSplittingCharPairMulTwist
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMP

noncomputable section

theorem jdl_pow (d : ℕ) (ν : Fin (d + 1) → ℝ) (hν : Function.Injective ν) (k : ℕ) (hk : k ≤ d) (y : ℂ) :
    y ^ k = ∑ j, lagC ν j y * ((ν j : ℝ) : ℂ) ^ k := by
  classical
  have hinj : Set.InjOn (fun j : Fin (d + 1) => ((ν j : ℝ) : ℂ)) (Finset.univ : Finset (Fin (d + 1))) :=
    fun a _ b _ h => hν (Complex.ofReal_injective h)
  have hdeg : (Polynomial.X ^ k : Polynomial ℂ).degree < (Finset.univ : Finset (Fin (d + 1))).card := by
    rw [Finset.card_univ, Fintype.card_fin, Polynomial.degree_X_pow]
    exact_mod_cast Nat.lt_succ_of_le hk
  have hf := Lagrange.eq_interpolate hinj hdeg
  have h := congrArg (Polynomial.eval y) hf
  rw [Lagrange.interpolate_apply, Polynomial.eval_finsetSum, Polynomial.eval_pow, Polynomial.eval_X] at h
  rw [h]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X, mul_comm]
  congr 1
  unfold lagC Lagrange.basis
  rw [Polynomial.eval_prod]
  refine Finset.prod_congr rfl fun i _ => ?_
  simp only [Lagrange.basisDivisor, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_sub, Polynomial.eval_X]
  rw [div_eq_inv_mul]

theorem jdl_interp {R : Type} [Ring R] [Algebra ℂ R] (f : ℂ → R) (d : ℕ)
    (hf : Formalism.FourierDecayAlt.P.MAx3.G.PolyIn (fun s => f (0 + s)) d) (ν : Fin (d + 1) → ℝ) (hν : Function.Injective ν)
    (y : ℂ) : f y = ∑ j, lagC ν j y • f ((ν j : ℝ) : ℂ) := by
  obtain ⟨a, ha⟩ := hf
  have hf' : ∀ s, f s = ∑ k ∈ Finset.range (d + 1), s ^ k • a k := fun s => by simpa using ha s
  have e1 : f y = ∑ k ∈ Finset.range (d + 1), (∑ j, lagC ν j y * ((ν j : ℝ) : ℂ) ^ k) • a k := by
    rw [hf' y]
    refine Finset.sum_congr rfl fun k hk => ?_
    rw [← jdl_pow d ν hν k (Nat.lt_succ_iff.1 (Finset.mem_range.1 hk)) y]
  rw [e1]
  simp only [hf', Finset.sum_smul, Finset.smul_sum, smul_smul]
  exact Finset.sum_comm

theorem hat_lagrange_decay_holds : JDHatLagrange := by
  intro P L ν hν y
  exact ⟨jdl_interp (fun s => L.R0 s) (P.r + 1) (Formalism.FourierDecayAlt.P.MAx3.G.raising_operator_polynomial P L 0) ν hν y,
    jdl_interp (fun s => L.R0v s) (P.r + 1) (Formalism.FourierDecayAlt.P.MAx3.L.raising_variant_polynomial P L 0) ν hν y⟩

end

end Formalism.FourierDecayAlt.P.CutMP
