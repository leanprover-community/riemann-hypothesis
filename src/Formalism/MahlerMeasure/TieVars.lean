module

public import Formalism.MahlerMeasure.LevelSum
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init

@[expose] public section

namespace Formalism.GM.M

open MvPolynomial Finset

noncomputable def fockK {k σ : Type} [Field k] (F G : MvPolynomial σ k) : k :=
  ∑ m ∈ F.support, F.coeff m * G.coeff m * (m.prod fun _ j => (j.factorial : k))

noncomputable def tieEh {k σ : Type} [Field k] {r : ℕ} (w e : Fin r → σ) (zv sv : σ) :
    MvPolynomial σ k →ₗ[k] MvPolynomial σ k :=
  LinearMap.mulLeft k (X zv * X sv + ∑ c, X (w c) * X (e c))

noncomputable def tieFh {k σ : Type} [Field k] {r : ℕ} (w e : Fin r → σ) (zv sv : σ) :
    MvPolynomial σ k →ₗ[k] MvPolynomial σ k :=
  (pderiv zv).toLinearMap ∘ₗ (pderiv sv).toLinearMap + Formalism.GM.tieF w e

noncomputable def tieP {k σ : Type} [Field k] {r : ℕ} (w e : Fin r → σ) (zv sv : σ) (o n z : ℕ)
    (y : MvPolynomial σ k) : MvPolynomial σ k :=
  ∑ l ∈ range (o + 1),
    (((-1 : k) ^ l) / (((l.factorial : k) ^ 2) * ((o + n + r + z - 1).choose l : k))) •
      ((tieEh w e zv sv) ^ l) (((Formalism.GM.tieF w e) ^ l) (X zv ^ z * y))

def TieVars {σ : Type} {r : ℕ} (w e : Fin r → σ) (zv sv : σ) : Prop :=
  Function.Injective w ∧ Function.Injective e ∧ (∀ c d, w c ≠ e d) ∧ (∀ c, w c ≠ zv ∧ w c ≠ sv ∧ e c ≠ zv ∧
    e c ≠ sv) ∧ zv ≠ sv

def ZSFree {k σ : Type} [Field k] (zv sv : σ) (y : MvPolynomial σ k) : Prop :=
  ∀ m ∈ y.support, m zv = 0 ∧ m sv = 0

end Formalism.GM.M
