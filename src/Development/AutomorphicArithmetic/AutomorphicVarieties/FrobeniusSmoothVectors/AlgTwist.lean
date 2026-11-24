module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.LeAdicClosure
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
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr

private theorem w_rev (n : ℕ) (i : Fin n) : w n i.rev = - w n i := by
  have := i.isLt
  simp only [w, Fin.val_rev]
  split_ifs <;> omega

private theorem J_apply {K : Type} [CommRing K] {n : ℕ} (X : Matrix (Fin n) (Fin n) K) (i j : Fin n) :
    (Jmat (R := K) n * Xᵀ * Jmat (R := K) n) i j = X j.rev i.rev := by
  simp only [Matrix.mul_apply, Jmat, Matrix.transpose_apply, ite_mul, one_mul, zero_mul,
    mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  have key : ∀ k : Fin n, (j = k.rev) ↔ (k = j.rev) := by
    intro k
    constructor
    · rintro rfl
      simp
    · rintro rfl
      simp
  simp only [key, Finset.sum_ite_eq', Finset.mem_univ, if_true]

private def tw {K : Type} [CommRing K] (n : ℕ) (u : Kˣ) :
    Matrix (Fin n) (Fin n) K →ₐ[K] Matrix (Fin n) (Fin n) K where
  toFun X := Matrix.of fun i j => ((u ^ (w n i - w n j) : Kˣ) : K) * X i j
  map_one' := by
    ext i j
    by_cases h : i = j <;> simp [h, Matrix.one_apply]
  map_mul' X Y := by
    ext i j
    simp only [Matrix.of_apply, Matrix.mul_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    have : w n i - w n j = (w n i - w n a) + (w n a - w n j) := by ring
    rw [this, _root_.zpow_add, Units.val_mul]
    ring
  map_zero' := by ext i j; simp
  map_add' X Y := by ext i j; simp [mul_add]
  commutes' c := by
    ext i j
    by_cases h : i = j <;> simp [h, Matrix.algebraMap_matrix_apply]

private theorem tw_apply {K : Type} [CommRing K] (n : ℕ) (u : Kˣ) (X : Matrix (Fin n) (Fin n) K) (i j : Fin n) :
    tw n u X i j = ((u ^ (w n i - w n j) : Kˣ) : K) * X i j := rfl

private theorem ordProd_tw {H K : Type} [CommRing K] {n : ℕ} (u : Kˣ)
    (r : H → Matrix (Fin n) (Fin n) K) (ψ : Fin n → H → K) (g : Fin n → H) :
    ordProd (fun s => tw n u (r s)) ψ g = tw n u (ordProd r ψ g) := by
  unfold ordProd
  rw [map_list_prod, List.map_ofFn]
  congr 2
  funext i
  simp

theorem UpperTheory.V.Fr.alg_twist :
    ∀ {l : ℕ} [Fact l.Prime] {k : Type} [Field k] {F : Frame l k} {n : ℕ} {K : Type} [CommRing K] (u : Kˣ) (ρ : NRep F n K), ∃ ρ' : NRep F n K, (∀ g i j, ρ'.r g i j = ((u ^ (w n i - w n j) : Kˣ) : K) * ρ.r g i j) ∧ ρ'.ψ = ρ.ψ := by
  intro l _ k _ F n K _ u ρ
  refine ⟨⟨(tw n u).toRingHom.toMonoidHom.comp ρ.r, ρ.ψ, ?_, ?_, ?_⟩, fun g i j => rfl, rfl⟩
  · intro g
    ext i j
    rw [J_apply]
    show tw n u (ρ.r (F.star g)) i j = tw n u (ρ.r g) j.rev i.rev
    rw [tw_apply, tw_apply, ρ.pol, J_apply, w_rev, w_rev]
    congr 3
    ring
  · intro i j h
    have := ρ.diag i j h
    rw [Matrix.sub_apply] at this ⊢
    show tw n u (ρ.r F.g0) i j - tw n u (ρ.r (F.star F.g0)) i j = 0
    rw [tw_apply, tw_apply, ← mul_sub, this, mul_zero]
  · intro v g
    have := ordProd_tw u (fun s => ρ.r (F.loc0 v s)) (fun i s => ((ρ.ψ v i s : Kˣ) : K)) g
    exact this.trans (by rw [ρ.ord, map_zero])
