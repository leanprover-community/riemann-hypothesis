module

public import Formalism.LocalToGlobal.HermitianForms.FormsTied
public import Formalism.SharpRestriction.GlobalSchurBounds.ProductFirstZerothParts
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

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.LocalLatticeBases

open Formalism.BasicNotions Formalism.MainNotions.product_first_zeroth_parts

variable (D : D7) (u : D.what₂.Word)

theorem emb_tpow_smul (i n : ℕ) (x : ((D.fm u).lat i).V) :
    (D.fm u).emb i (((D.mem u).A.T : D.what₂.LL) ^ n • x) = tpow D u n • (D.fm u).emb i x := by
  rw [LinearMap.map_smulₛₗ, map_pow, map_natCast]
  rfl

theorem eval_subP {ι : Type} [Fintype ι] {n : ℕ} (N Z : ι → Matrix (Fin n) (Fin n) ℂ)
    (P : MvPolynomial (ι × Fin n × Fin n) ℂ) :
    MvPolynomial.eval (fun x : ι × Fin n × Fin n => (N x.1 * Z x.1) x.2.1 x.2.2) P =
      MvPolynomial.eval (fun x : ι × Fin n × Fin n => Z x.1 x.2.1 x.2.2) (Formalism.L2.Forms.subP N P) := by
  induction P using MvPolynomial.induction_on with
  | C a => simp [Formalism.L2.Forms.subP]
  | add p q hp hq => simp [hp, hq]
  | mul_X p x hp =>
    simp only [map_mul, MvPolynomial.eval_X, hp]
    simp [Formalism.L2.Forms.subP, Matrix.mul_apply]

theorem fnOf_mul {ι : Type} [Fintype ι] {n : ℕ} (G : ι → Matrix (Fin n) (Fin n) ℂ) (s : ι → ℤ)
    (N M : ι → Matrix (Fin n) (Fin n) ℂ) (P : MvPolynomial (ι × Fin n × Fin n) ℂ) :
    Formalism.L2.Forms.fnOf G s (fun τ => N τ * M τ) P =
      Formalism.L2.Forms.fnOf G s M (MvPolynomial.C (∏ τ, (N τ).det ^ s τ) * Formalism.L2.Forms.subP N P) := by
  funext y
  simp only [Formalism.L2.Forms.fnOf, LinearMap.coe_mk, AddHom.coe_mk, map_mul, MvPolynomial.eval_C]
  have h := eval_subP N (fun τ => M τ * y.1 τ) P
  simp only [← Matrix.mul_assoc] at h
  rw [h]
  simp only [Matrix.mul_assoc (N _), Matrix.det_mul, mul_zpow, Finset.prod_mul_distrib]
  ring

end Formalism.L2.GlobalTheoryTheory.LocalLatticeBases
