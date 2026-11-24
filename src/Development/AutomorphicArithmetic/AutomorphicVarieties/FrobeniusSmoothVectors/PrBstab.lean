module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.PresDefs
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr

private theorem upT_mul {C : Type} [CommRing C] {n : ℕ} {M N : Matrix (Fin n) (Fin n) C}
    (hM : UpT M) (hN : UpT N) : UpT (M * N) := by
  intro i j h
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_zero fun a _ => ?_
  by_cases ha : a < i
  · rw [hM i a ha, zero_mul]
  · rw [hN a j (lt_of_lt_of_le h (not_lt.mp ha)), mul_zero]

theorem UpperTheory.V.Fr.pr_bstab :
    ∀ {l : ℕ} [Fact l.Prime] {k : Type} [Field k] {F : Frame l k} {n : ℕ}, ∀ (C : Type) [CommRing C] (B : Box F n C) (v : F.V) (s : F.Gv v), ∀ X ∈ B.b v, B.ad (F.loc v s) X ∈ B.b v := by
  intro l _ k _ F n C _ B v s X hX
  have h1 : (B.r (F.loc v s)).right = 1 := (B.nu _).trans (F.loc0 v s).2
  have h2 : (B.r (F.loc v s⁻¹)).left = (B.r (F.loc v s)).left⁻¹ := by
    rw [map_inv, map_inv, SemidirectProduct.inv_left, h1, inv_one, sgnAct_one]
  have t1 := B.tri v s
  have t2 := B.tri v s⁻¹
  have t3 := upT_mul (upT_mul t1 hX) t2
  simp only [GG.mat, h2] at t3
  show UpT ((B.g v : Matrix (Fin n) (Fin n) C) * (B.r (F.loc v s)).adFun X *
    (((B.g v)⁻¹ : GL (Fin n) C) : Matrix (Fin n) (Fin n) C))
  have hg : ∀ Y : Matrix (Fin n) (Fin n) C,
      (((B.g v)⁻¹ : GL (Fin n) C) : Matrix (Fin n) (Fin n) C) * ((B.g v : Matrix (Fin n) (Fin n) C) * Y) = Y :=
    fun Y => Units.inv_mul_cancel_left _ Y
  simp only [Matrix.mul_assoc, hg] at t3
  simp only [GG.adFun, GG.mat, h1, if_true, Matrix.mul_assoc]
  exact t3
