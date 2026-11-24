module

public import Development.AutomorphicArithmetic.Foundations.Convolution.HermitianDescent.NormAlmostAll
public import Development.AutomorphicArithmetic.Foundations.Convolution.HermitianDescent.ConjSep
public import Development.AutomorphicArithmetic.Foundations.Convolution.HermitianDescent.GalBase
public import Development.AutomorphicArithmetic.Foundations.Convolution.HermitianDescent.NmPoly
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
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

open Matrix Polynomial

namespace UpperTheory.ConvolutionTheory.D

section

variable {k R : Type} [CommRing k] [CommRing R] [Algebra k R] {n : ℕ}

private theorem rep_sg_succ (σ : R ≃ₐ[k] R) (i : ℕ) (d : GL (Fin n) R) :
    sg (σ ^ (i + 1)) d = sg σ (sg (σ ^ i) d) := by
  ext a b
  simp [sg, pow_succ', Matrix.GeneralLinearGroup.map_apply]

private theorem rep_sg_one (d : GL (Fin n) R) : sg (1 : R ≃ₐ[k] R) d = d := by
  ext a b
  simp [sg, Matrix.GeneralLinearGroup.map_apply]

private theorem rep_sg_up (σ : R ≃ₐ[k] R) (γ : GL (Fin n) k) : sg σ (up R γ) = up R γ := by
  ext a b
  simp [sg, up, Matrix.GeneralLinearGroup.map_apply]

private theorem rep_nm_succ (σ : R ≃ₐ[k] R) (q : ℕ) (d : GL (Fin n) R) :
    nm σ (q + 1) d = nm σ q d * sg (σ ^ q) d := by
  simp [nm, List.range_succ]

private theorem rep_shift (σ : R ≃ₐ[k] R) (q : ℕ) (d : GL (Fin n) R) :
    d * sg σ (nm σ q d) = nm σ q d * sg (σ ^ q) d := by
  induction q with
  | zero => simp [nm, rep_sg_one]
  | succ q ih => rw [rep_nm_succ, map_mul, ← mul_assoc, ih, rep_sg_succ]

private theorem rep_cp_up (γ : GL (Fin n) k) : cp (up R γ) = (cp γ).map (algebraMap k R) := by
  rw [cp, cp, ← Matrix.charpoly_map]
  rfl

end

theorem nmRep : NmRep := by
  intro k R _ _ _ _ σ q hσ n δ γ hsep hcp
  haveI : Module.Finite k R := (galBase k R k σ q hσ).1
  have hs : ((nm σ q δ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R).charpoly.Separable := by
    have h := hsep.map (f := algebraMap k R)
    rwa [← hcp] at h
  obtain ⟨x, hx⟩ := (conjSep k R n _ hs).1 ((up R γ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R)
    ((rep_cp_up γ).trans hcp.symm)
  have hx' : nm σ q δ * x = x * up R γ := Units.ext (by simpa using hx)
  have h1 : nm σ q (sgConj σ x δ) = up R γ := by
    rw [(nmPoly k R σ q hσ n δ).2 x, mul_assoc, hx', inv_mul_cancel_left]
  refine ⟨x, h1, ?_⟩
  have h2 := rep_shift σ q (sgConj σ x δ)
  rw [h1, rep_sg_up, hσ.pow, rep_sg_one] at h2
  exact h2

end UpperTheory.ConvolutionTheory.D
