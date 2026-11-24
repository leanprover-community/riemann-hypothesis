module

public import Formalism.RealPlaceAnalysis.StatementE
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Topology.Sheaves.Init
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.WeylAlgebraQuantumDet.IsTop

@[expose] public section

open Matrix UpperTheory.V.Weyl

theorem UpperTheory.V.Weyl.qdetRect :
    ∀ (n d d' : ℕ) (E : Fin n → Fin n → Matrix (Fin d) (Fin d) ℂ) (E' : Fin n → Fin n → Matrix (Fin d') (Fin d') ℂ)
      (A : Matrix (Fin d) (Fin d') ℂ), (∀ a b, E a b * A = A * E' a b) → ∀ u : ℂ, Formalism.REAL.qdet E u * A = A * Formalism.REAL.qdet E' u := by
  intro n d d' E E' A h u
  have hs : ∀ v : ℂ, (algebraMap ℂ (Matrix (Fin d) (Fin d) ℂ) v) * A = A * algebraMap ℂ (Matrix (Fin d') (Fin d') ℂ) v := by
    intro v
    rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, Matrix.smul_mul, Matrix.mul_smul,
      Matrix.one_mul, Matrix.mul_one]
  have hT : ∀ (v : ℂ) a b, Formalism.REAL.Tm E v a b * A = A * Formalism.REAL.Tm E' v a b := by
    intro v a b
    simp only [Formalism.REAL.Tm]
    rw [Matrix.add_mul, Matrix.mul_add, h]
    split_ifs
    · rw [hs]
    · rw [Matrix.zero_mul, Matrix.mul_zero]
  have hL : ∀ (m : ℕ) (f : Fin m → Matrix (Fin d) (Fin d) ℂ) (g : Fin m → Matrix (Fin d') (Fin d') ℂ),
      (∀ k, f k * A = A * g k) → (List.ofFn f).prod * A = A * (List.ofFn g).prod := by
    intro m
    induction m with
    | zero => intro f g _; simp
    | succ m ih =>
      intro f g hfg
      rw [List.ofFn_succ, List.ofFn_succ, List.prod_cons, List.prod_cons, Matrix.mul_assoc,
        ih _ _ (fun k => hfg k.succ), ← Matrix.mul_assoc, hfg 0, Matrix.mul_assoc]
  have hz : ∀ z : ℤ, (z : Matrix (Fin d) (Fin d) ℂ) * A = A * (z : Matrix (Fin d') (Fin d') ℂ) := by
    intro z
    rw [← map_intCast (algebraMap ℂ (Matrix (Fin d) (Fin d) ℂ)), ← map_intCast (algebraMap ℂ (Matrix (Fin d') (Fin d') ℂ))]
    exact hs _
  simp only [Formalism.REAL.qdet, Formalism.REAL.qminor]
  rw [Matrix.sum_mul, Matrix.mul_sum]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [Matrix.mul_assoc, hL _ _ _ (fun k => hT _ _ _), ← Matrix.mul_assoc, hz, Matrix.mul_assoc]
