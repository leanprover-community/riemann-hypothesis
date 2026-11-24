module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProdMinorsMemInv
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

@[expose] public section

noncomputable section

open MvPolynomial

namespace GlobalTheory.MinorFrame

def rsub {σ σ' : Type} [Fintype σ'] (M : Matrix σ' σ ℂ) : MvPolynomial σ ℂ →ₐ[ℂ] MvPolynomial σ' ℂ :=
  aeval fun v => ∑ w, C (M w v) * X w

theorem rsub_X {σ σ' : Type} [Fintype σ'] (M : Matrix σ' σ ℂ) (v : σ) :
    rsub M (X v) = ∑ w, C (M w v) * X w := aeval_X _ _

variable {ι : Type}

open Classical in
def frameMat {d a : ℕ} (x₀ : Var ι d a → ℂ) : Matrix (ι × Fin a × Fin a) (Var ι d a) ℂ :=
  by
    classical
    exact fun w v => if w.1 = v.1 ∧ w.2.2 = v.2.2 then x₀ (v.1, v.2.1, w.2.1) else 0

def detG [Fintype ι] (a : ℕ) (n : ι → ℕ) : MvPolynomial (ι × Fin a × Fin a) ℂ :=
  ∏ τ, (Matrix.of fun i j : Fin a => (X (τ, i, j) : MvPolynomial (ι × Fin a × Fin a) ℂ)).det ^ n τ

theorem eval_detG [Fintype ι] (a : ℕ) (n : ι → ℕ) (g : ι → Matrix (Fin a) (Fin a) ℂ) :
    eval (fun v : ι × Fin a × Fin a => g v.1 v.2.1 v.2.2) (detG a n) = detChar n g := by
  unfold detG detChar
  rw [map_prod]
  refine Finset.prod_congr rfl fun τ _ => ?_
  rw [map_pow, RingHom.map_det]
  congr 2
  ext i j
  simp

theorem detG_ne_zero [Fintype ι] (a : ℕ) (n : ι → ℕ) : detG (ι := ι) a n ≠ 0 := by
  intro h
  have := eval_detG (ι := ι) a n (fun _ => 1)
  rw [h, map_zero] at this
  simp [detChar] at this

end GlobalTheory.MinorFrame
