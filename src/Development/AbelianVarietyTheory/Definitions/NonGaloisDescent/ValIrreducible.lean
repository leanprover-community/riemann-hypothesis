module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnitLemmaGroup
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

namespace GlobalTheory.UnitLemma.Basic

variable {K : UQ} (B : InvAlg K)

variable {K : _root_.GlobalTheory.UnitLemma.UQ} (B : _root_.GlobalTheory.UnitLemma.InvAlg K) in
private theorem sigma_smul_eq_conj_smul (e : K.E) (v : B.A) : B.σ (e • v) = K.c e • B.σ v := by
  rw [Algebra.smul_def, map_mul, B.σ_alg, ← Algebra.smul_def]


variable {K : _root_.GlobalTheory.UnitLemma.UQ} (B : _root_.GlobalTheory.UnitLemma.InvAlg K) in
theorem _root_.GlobalTheory.UnitLemma.Basic.trace_sigma (u : B.A) :
    Algebra.trace K.E B.A (B.σ u) = K.c (Algebra.trace K.E B.A u) := by
  classical
  set b := Module.finBasis K.E B.A
  let φ : B.A ≃ₗ[K.E] (Fin (Module.finrank K.E B.A) → K.E) :=
    { toFun := fun v i => K.c (b.repr (B.σ v) i)
      map_add' := fun v w => by ext i; simp
      map_smul' := fun e v => by ext i; simp [sigma_smul_eq_conj_smul, K.c_c]
      invFun := fun f => B.σ (∑ i, K.c (f i) • b i)
      left_inv := fun v => by
        simp only [K.c_c, b.sum_repr, B.σ_σ]
      right_inv := fun f => by
        ext i
        simp [B.σ_σ, Finsupp.single_apply, K.c_c] }
  let b' := Module.Basis.ofEquivFun φ
  have hb' (j) : b' j = B.σ (b j) := by
    simp [b', Module.Basis.coe_ofEquivFun, φ, Pi.single_apply, apply_ite B.σ]
  have hrepr (w : B.A) (i) : b'.repr w i = K.c (b.repr (B.σ w) i) := by
    simp [b', φ]

  rw [Algebra.trace_eq_matrix_trace b' (B.σ u), Algebra.trace_eq_matrix_trace b u,
  Matrix.trace, Matrix.trace, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Matrix.diag, Algebra.leftMulMatrix_apply, LinearMap.toMatrix_apply,
    Algebra.coe_lmul_eq_mul, LinearMap.mul_apply', hb', hrepr, ← map_mul, B.σ_σ]


variable {K : _root_.GlobalTheory.UnitLemma.UQ} (B : _root_.GlobalTheory.UnitLemma.InvAlg K) in
theorem _root_.GlobalTheory.UnitLemma.Basic.herm_smul_left (x y z : B.A) (e : K.E) :
    B.herm x (e • y) z = e * B.herm x y z := by
  unfold _root_.GlobalTheory.UnitLemma.InvAlg.herm
  rw [mul_smul_comm, smul_mul_assoc, map_smul, smul_eq_mul]


variable {K : _root_.GlobalTheory.UnitLemma.UQ} (B : _root_.GlobalTheory.UnitLemma.InvAlg K) in
theorem _root_.GlobalTheory.UnitLemma.Basic.herm_smul_right (x y z : B.A) (e : K.E) :
    B.herm x y (e • z) = K.c e * B.herm x y z := by
  unfold _root_.GlobalTheory.UnitLemma.InvAlg.herm
  rw [sigma_smul_eq_conj_smul, mul_smul_comm, map_smul, smul_eq_mul]


variable {K : _root_.GlobalTheory.UnitLemma.UQ} (B : _root_.GlobalTheory.UnitLemma.InvAlg K) in
theorem _root_.GlobalTheory.UnitLemma.Basic.herm_symm (x : B.A) (hx : B.σ x = x) (y z : B.A) :
    B.herm x z y = K.c (B.herm x y z) := by
  unfold _root_.GlobalTheory.UnitLemma.InvAlg.herm
  rw [← _root_.GlobalTheory.UnitLemma.Basic.trace_sigma, map_mul B.σ, map_mul B.σ, hx, B.σ_σ]
  congr 1
  ring


variable {K : _root_.GlobalTheory.UnitLemma.UQ} (B : _root_.GlobalTheory.UnitLemma.InvAlg K) in
theorem _root_.GlobalTheory.UnitLemma.Basic.herm_mul_left (x u y z : B.A) :
    B.herm x (u * y) z = B.herm x y (B.σ u * z) := by
  unfold _root_.GlobalTheory.UnitLemma.InvAlg.herm
  rw [map_mul B.σ, B.σ_σ]
  congr 1
  ring


variable {K : _root_.GlobalTheory.UnitLemma.UQ} (B : _root_.GlobalTheory.UnitLemma.InvAlg K) in
theorem _root_.GlobalTheory.UnitLemma.Basic.herm_norm (x u y z : B.A) :
    B.herm (x * (u * B.σ u)) y z = B.herm x (u * y) (u * z) := by
  unfold _root_.GlobalTheory.UnitLemma.InvAlg.herm
  rw [map_mul B.σ]
  congr 1
  ring

end GlobalTheory.UnitLemma.Basic
