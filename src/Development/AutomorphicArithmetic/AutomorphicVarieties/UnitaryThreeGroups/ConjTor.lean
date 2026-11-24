module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.BaseRepGL3NormalisedOfPsiEqOne
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

open Matrix UpperTheory.V.U3

private theorem sgnAct_tor {R : Type} [CommRing R] (s : ℤˣ) (t : Rˣ) :
    sgnAct (m := 3) (R := R) s (tor R t) = tor R t := by
  rcases Int.units_eq_one_or s with rfl | rfl <;> simp [theta_tor]

private theorem conj_left {G R : Type} [Group G] [CommRing R] (r : G →* GG (m := 3) (R := R)) (t : Rˣ) (g : G) :
    (conjBy (tor R t) r g).left = tor R t * (r g).left * tor R t⁻¹ := by
  simp [conjBy, MulAut.conj_apply, SemidirectProduct.mul_left, SemidirectProduct.inv_left, sgnAct_tor, map_inv]

private theorem conj_right {G R : Type} [Group G] [CommRing R] (r : G →* GG (m := 3) (R := R)) (t : Rˣ) (g : G) :
    (conjBy (tor R t) r g).right = (r g).right := by
  simp [conjBy, MulAut.conj_apply, SemidirectProduct.mul_right, SemidirectProduct.inv_right]

private theorem conj_mat {G R : Type} [Group G] [CommRing R] (r : G →* GG (m := 3) (R := R)) (t : Rˣ) (g : G)
    (a b : Fin 3) :
    (conjBy (tor R t) r g).mat a b = ((t ^ wt a b : Rˣ) : R) * (r g).mat a b := by
  show (((conjBy (tor R t) r g).left : GL (Fin 3) R) : Matrix (Fin 3) (Fin 3) R) a b = _
  rw [conj_left, Units.val_mul, Units.val_mul, tor_val, tor_val, mul_diagonal, diagonal_mul]
  have key : ((t ^ wt1 a : Rˣ) : R) * ((t⁻¹ ^ wt1 b : Rˣ) : R) = ((t ^ wt a b : Rˣ) : R) := by
    rw [← Units.val_mul, wt, _root_.zpow_sub, _root_.inv_zpow]
  rw [← key, GG.mat]
  ring

private theorem conj_zmat {G R : Type} [Group G] [CommRing R] (r : G →* GG (m := 3) (R := R)) (t : Rˣ) (c g₁ : G)
    (a b : Fin 3) :
    zmat c g₁ (conjBy (tor R t) r) a b = ((t ^ wt a b : Rˣ) : R) * zmat c g₁ r a b := by
  simp only [zmat, Matrix.sub_apply, conj_mat, mul_sub]

theorem UpperTheory.V.U3.conjBy_tor :
    ∀ {G R : Type} [Group G] [CommRing R] (r : G →* GG (m := 3) (R := R)) (t : Rˣ),
    (∀ g a b, (conjBy (tor R t) r g).mat a b = ((t ^ wt a b : Rˣ) : R) * (r g).mat a b) ∧ (∀ g, (conjBy (tor R t) r g).right = (r g).right) ∧
    (∀ c g₁, Normalised c g₁ r → Normalised c g₁ (conjBy (tor R t) r)) ∧ (∀ c g₁, zeta c g₁ (conjBy (tor R t) r) = zeta c g₁ r) ∧
    ∀ (η : G →* ℤˣ) (Ψ : G →* Rˣ), conjBy (tor R t) (r0 η Ψ) = r0 η Ψ := by
  intro G R _ _ r t
  refine ⟨conj_mat r t, conj_right r t, ?_, ?_, ?_⟩
  · intro c g₁ h
    refine ⟨?_, ?_, ?_⟩
    · ext a b
      rw [conj_mat, h.atc]
      by_cases hab : a = b
      · subst hab
        simp [wt]
      · simp [Matrix.one_apply_ne hab]
    · rw [conj_zmat, h.z12, mul_zero]
    · rw [conj_zmat, h.z21, mul_zero]
  · intro c g₁
    unfold zeta
    rw [conj_zmat]
    simp [wt]
  · intro η Ψ
    refine MonoidHom.ext fun g => ?_
    refine SemidirectProduct.ext ?_ (conj_right _ t g)
    rw [conj_left, unitaryThreeReflection_left, ← map_mul, ← map_mul, mul_inv_cancel_comm]
