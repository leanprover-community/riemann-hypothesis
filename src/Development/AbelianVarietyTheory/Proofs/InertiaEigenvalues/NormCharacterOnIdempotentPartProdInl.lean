module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DltEqZero
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
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Desc Polynomial Filter Topology

namespace GlobalTheory.UnitLemma.Desc

theorem norm_prod_mk_one {K : UQ} (B₁ B₂ : InvAlg K) (y : B₁.A) :
    Algebra.norm K.E ((y, 1) : B₁.A × B₂.A) = Algebra.norm K.E y := by
  rw [Algebra.norm_apply, Algebra.norm_apply]
  have h : Algebra.lmul K.E (B₁.A × B₂.A) (y, 1) =
      LinearMap.prodMap (Algebra.lmul K.E B₁.A y) (Algebra.lmul K.E B₂.A 1) := by
    ext z <;> simp
  rw [h, LinearMap.det_prodMap, map_one, map_one, mul_one]

theorem chi_prod_inl : ∀ (K : UQ) (B₁ B₂ : InvAlg K) (ι₁ ι₂ : Type) (e₁ : ι₁ → B₁.A) (e₂ : ι₂ → B₂.A) (S₁ : Finset ι₁) (x : B₁.A × B₂.A), chi (B₁.prod B₂) (Sum.elim (fun i => ((e₁ i, 0) : B₁.A × B₂.A)) (fun j => ((0, e₂ j) : B₁.A × B₂.A))) (S₁.map Function.Embedding.inl) x = chi B₁ e₁ S₁ x.1 := by
  intro K B₁ B₂ ι₁ ι₂ e₁ e₂ S₁ x
  have hS : eS (B₁.prod B₂) (Sum.elim (fun i => ((e₁ i, 0) : B₁.A × B₂.A)) (fun j => ((0, e₂ j) : B₁.A × B₂.A)))
      (S₁.map Function.Embedding.inl) = ((eS B₁ e₁ S₁, 0) : B₁.A × B₂.A) := by
    unfold eS
    rw [Finset.sum_map]
    show (∑ i ∈ S₁, ((e₁ i, 0) : B₁.A × B₂.A)) = ((∑ i ∈ S₁, e₁ i, 0) : B₁.A × B₂.A)
    rw [Prod.ext_iff]
    simp [Prod.fst_sum, Prod.snd_sum]
  unfold chi
  rw [hS]
  have hx : (x * ((eS B₁ e₁ S₁, 0) : B₁.A × B₂.A) + (1 - ((eS B₁ e₁ S₁, 0) : B₁.A × B₂.A)) : B₁.A × B₂.A) =
      ((x.1 * eS B₁ e₁ S₁ + (1 - eS B₁ e₁ S₁), 1) : B₁.A × B₂.A) := by
    ext <;> simp
  change K.eta (Algebra.norm K.E (x * ((eS B₁ e₁ S₁, 0) : B₁.A × B₂.A) + (1 - ((eS B₁ e₁ S₁, 0) : B₁.A × B₂.A)))) = _
  rw [hx, norm_prod_mk_one]

end GlobalTheory.UnitLemma.Desc
