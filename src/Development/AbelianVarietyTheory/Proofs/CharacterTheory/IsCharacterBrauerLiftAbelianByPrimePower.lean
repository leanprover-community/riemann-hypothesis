module

public import Development.AbelianVarietyTheory.Definitions.CommutativeAlgebra.AbByPOfComm
public import Mathlib.Basic.Complex.Basic
public import Mathlib.RingTheory.SimpleRing.Principal
public import Development.AbelianVarietyTheory.Proofs.CharacterTheory.ExistsMonomialBasisAbelianByPrimePowerStatement
public import Development.AbelianVarietyTheory.Proofs.CharacterTheory.TraceLiftMonomialMatrixEqSumEigenvaluesStatement
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.TotallySplit
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.CommutativeAlgebra.InvariantSubspaceMobiusInverseRecEqOfFinrankLt

@[expose] public section

open Polynomial GlobalTheory.CuspGL GlobalTheory.BI

namespace GlobalTheory.CuspGL

theorem basis_smul_eq_smul_cancel {k V ι : Type} [Field k] [AddCommGroup V] [Module k V]
    (b : Module.Basis ι k V) {x y : k} {i j : ι} (hx : x ≠ 0) (h : x • b i = y • b j) :
    i = j ∧ x = y := by
  classical
  have h1 := congrArg (fun v => b.repr v i) h
  simp only [map_smul, Module.Basis.repr_self, Finsupp.smul_apply, Finsupp.single_eq_same,
    smul_eq_mul, mul_one, Finsupp.single_apply] at h1
  by_cases hij : j = i
  · subst hij
    simpa using h1
  · simp [hij, hx] at h1

theorem isChar_brauerLift : ∀ (k : Type) [Field k] [IsAlgClosed k] (θ : k →* ℂ), (∀ x y : k, x ≠ 0 → y ≠ 0 → θ x = θ y → x = y) → ∀ (G : Type) [Group G] [Finite G], AbByP G → (Nat.card G : k) ≠ 0 → ∀ (n : ℕ) (ρ : G →* GL (Fin n) k), IsChar ℂ ℂ (fun g => ((Matrix.charpoly (ρ g : Matrix (Fin n) (Fin n) k)).roots.map θ).sum) := by
  intro k _ _ θ hθ G _ _ hG hc n ρ
  classical
  let R : Representation k G (Fin n → k) :=
    ((Matrix.toLinAlgEquiv' : Matrix (Fin n) (Fin n) k ≃ₐ[k] _).toMonoidHom.comp
      (Units.coeHom _)).comp ρ
  have hR : ∀ g, R g = Matrix.toLin' (ρ g : Matrix (Fin n) (Fin n) k) := fun g => rfl
  obtain ⟨m, b, hb⟩ := GlobalTheory.T.exists_monomial_basis_abelianByPrimePower k G (Fin n → k) R hG hc
  choose s c hsc using hb
  have hc0 : ∀ g i, c g i ≠ 0 := by
    intro g i h0
    have h1 : R g (b i) = 0 := by rw [hsc, h0, zero_smul]
    have h2 : R (g⁻¹ * g) (b i) = 0 := by
      rw [map_mul, Module.End.mul_apply, h1, map_zero]
    rw [inv_mul_cancel, map_one, Module.End.one_apply] at h2
    exact b.ne_zero i h2
  have hmul : ∀ g h i, s (g * h) i = s g (s h i) ∧ c (g * h) i = c g (s h i) * c h i := by
    intro g h i
    apply basis_smul_eq_smul_cancel b (hc0 _ _)
    rw [← hsc, map_mul, Module.End.mul_apply, hsc, map_smul, hsc, smul_smul, mul_comm]
  have hone : ∀ i, s 1 i = i ∧ c 1 i = 1 := by
    intro i
    apply basis_smul_eq_smul_cancel b (hc0 _ _)
    rw [← hsc, map_one, Module.End.one_apply, one_smul]
  let σ : G → Equiv.Perm (Fin m) := fun g =>
    { toFun := s g
      invFun := s g⁻¹
      left_inv := fun i => by rw [← (hmul _ _ _).1, inv_mul_cancel, (hone i).1]
      right_inv := fun i => by rw [← (hmul _ _ _).1, mul_inv_cancel, (hone i).1] }
  let L : G →* Matrix (Fin m) (Fin m) ℂ :=
    { toFun := fun g => Matrix.of fun i j => if i = σ g j then θ (c g j) else 0
      map_one' := by
        ext i j
        simp [σ, (hone j).1, (hone j).2, Matrix.one_apply]
      map_mul' := by
        intro g h
        ext i j
        simp [σ, Matrix.mul_apply, (hmul g h j).1, (hmul g h j).2] }
  have hM : ∀ g, (Matrix.of fun i j => if i = σ g j then c g j else 0 : Matrix (Fin m) (Fin m) k)
      = LinearMap.toMatrix b b (R g) := by
    intro g
    ext i j
    simp [σ, LinearMap.toMatrix_apply, hsc, Finsupp.single_apply, eq_comm]
  refine ⟨m, (Matrix.toLinAlgEquiv' : Matrix (Fin m) (Fin m) ℂ ≃ₐ[ℂ] _).toMonoidHom.comp L, fun g => ?_⟩
  have h1 : (Matrix.of fun i j => if i = σ g j then c g j else 0 : Matrix (Fin m) (Fin m) k)
      ^ Nat.card G = 1 := by
    rw [hM, LinearMap.toMatrix_pow, ← map_pow, pow_card_eq_one', map_one, LinearMap.toMatrix_one]
  have h2 : L g ^ Nat.card G = 1 := by rw [← map_pow, pow_card_eq_one', map_one]
  have h3 := GlobalTheory.T.trace_lift_monomialMatrix_eq_sum_eigenvalues k θ hθ m (Nat.card G) (σ g) (c g) (hc0 g) hc h1 h2
  rw [hM, LinearMap.charpoly_toMatrix, hR, Matrix.charpoly_toLin'] at h3
  show _ = LinearMap.trace ℂ _ (Matrix.toLin' (L g))
  rw [Matrix.trace_toLin'_eq]
  exact h3.symm

end GlobalTheory.CuspGL
