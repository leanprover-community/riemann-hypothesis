module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TranslateMemCoefLatFn
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum IsDedekindDomain NumberField GlobalTheory.ExportSeries
open Formalism.IndefR.Links
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ExportSeries

open MvPolynomial Matrix

theorem eq_zero_of_coefFn_id_eq_zero (D : D7) (n : ℕ) (lam : D.what₂.Tau → DomWeight n) (F : Formalism.L2.DIV.Pol ℂ D.what₂.Tau n)
    (hF : ∀ x : GLR D n, coefFn (RingHom.id ℂ) lam F x = 0) : F = 0 := by
  classical
  set d : MvPolynomial (D.what₂.Tau × Fin n × Fin n) ℂ :=
    ∏ τ, (Matrix.of fun a b => (X (τ, a, b) : MvPolynomial (D.what₂.Tau × Fin n × Fin n) ℂ)).det with hd
  have hev : ∀ v : D.what₂.Tau × Fin n × Fin n → ℂ, eval v d = ∏ τ, (Matrix.of fun a b => v (τ, a, b)).det := by
    intro v
    rw [hd, map_prod]
    refine Finset.prod_congr rfl fun τ _ => ?_
    rw [RingHom.map_det]
    congr 1
    ext a b
    rw [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply, Matrix.of_apply, eval_X]
  have hd0 : d ≠ 0 := by
    intro h
    have := hev (fun w => (1 : Matrix (Fin n) (Fin n) ℂ) w.2.1 w.2.2)
    rw [h, map_zero] at this
    have h1 : ∀ τ : D.what₂.Tau, (Matrix.of fun a b => (1 : Matrix (Fin n) (Fin n) ℂ) a b).det = 1 := by
      intro τ
      have : (Matrix.of fun a b => (1 : Matrix (Fin n) (Fin n) ℂ) a b) = 1 := by ext a b; rfl
      rw [this, det_one]
    rw [Finset.prod_eq_one fun τ _ => h1 τ] at this
    exact zero_ne_one this
  have hFd : F * d = 0 := by
    apply MvPolynomial.funext
    intro v
    rw [map_mul, map_zero, hev]
    by_cases h : ∏ τ, (Matrix.of fun a b => v (τ, a, b)).det = 0
    · rw [h, mul_zero]
    · have hτ : ∀ τ, (Matrix.of fun a b => v (τ, a, b)).det ≠ 0 := fun τ hτ =>
        h (Finset.prod_eq_zero (Finset.mem_univ τ) hτ)
      let x : GLR D n := fun τ => GeneralLinearGroup.mkOfDetNeZero _ (hτ τ)
      have hx := hF x
      rw [coefFn] at hx
      have hu : ((detFam (fun τ => (lam τ).detShift) x : ℂˣ) : ℂ) ≠ 0 := Units.ne_zero _
      have h2 := (mul_eq_zero.mp hx).resolve_left hu
      have h3 : (fun w : D.what₂.Tau × Fin n × Fin n => (x w.1).val w.2.1 w.2.2) = v := by
        funext w
        rfl
      rw [h3] at h2
      have h4 : eval v F = 0 := by
        rw [← h2]
        rfl
      rw [h4, zero_mul]
  exact (mul_eq_zero.mp hFd).resolve_right hd0

end GlobalTheory.ExportSeries
