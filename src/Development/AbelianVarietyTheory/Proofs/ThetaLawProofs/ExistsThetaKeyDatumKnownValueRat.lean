module

public import Development.AbelianVarietyTheory.Definitions.KeyFormula.GeomIntSelf
public import Mathlib.AlgebraicGeometry.EllipticCurve.Weierstrass
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaUnifAV
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.DualNumberRingHomExt
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsEllipticKeyDataValueEqDiscriminant
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsIsGrpPullbackPow
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsIsKeyPow
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsKeyPBRing
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.LatticeBlocks
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.MemNonzeroLocusConstMul
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.NormalFormsEqOfKeyDataIsoComplexStatement
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.ReduceModChar
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.GoodClass

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.KeyPow GlobalTheory.KeyFam GlobalTheory.ZM GlobalTheory.AbLaw

namespace GlobalTheory.KeyFam

theorem Val.pow {x y : KeyIn ℂ} {j : ℕ} {t : ℂ} (hp : IsKeyPow y x j) (h : Val x t) : Val y (t ^ j) := by
  obtain ⟨τ, M, a, b, c, ⟨ha, hb⟩, hc, hN, rfl⟩ := h
  have ea : a = fun k => (((a k).re : ℝ) : ℂ) := by
    funext k
    rcases ha k with h | h <;> rw [h] <;> norm_num
  have eb : b = fun k => (((b k).re : ℝ) : ℂ) := by
    funext k
    rcases hb k with h | h <;> rw [h] <;> norm_num
  rw [ea, eb] at hN
  obtain ⟨e, τ', M', hdet, hN'⟩ := normalAt_pow x y j τ M _ _ c hp hN
  refine ⟨τ', M', _, _, c ^ j, ⟨fun p => ?_, fun p => ?_⟩, pow_ne_zero _ hc, hN', ?_⟩
  · rw [← congrFun ea]; exact ha _
  · rw [← congrFun eb]; exact hb _
  · rw [hdet, div_pow, ← pow_mul, ← pow_mul, ← pow_mul, ← pow_mul, Nat.mul_comm 4, Nat.mul_comm 8]

theorem isElliptic_cube_sub : (⟨0, 0, 0, -1, 0⟩ : WeierstrassCurve ℚ).IsElliptic := by
  refine ⟨Ne.isUnit ?_⟩
  norm_num [WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆, WeierstrassCurve.b₈]

theorem exists_known_rat : Out.Laws → ThetaUnifAV → ∀ g : ℕ, 1 ≤ g → ∃ y : KeyIn ℚ, y.P.g = g ∧ Known ℚ y := by
  intro _ hU g hg
  have := isElliptic_cube_sub
  obtain ⟨y₁, h₁, hval⟩ := EllipticKey.exists_keyIn_value_eq_discriminant hU ℚ ⟨0, 0, 0, -1, 0⟩
  obtain ⟨y, hy⟩ := exists_isKeyPow ℚ y₁ g hg
  refine ⟨y, ?_, (⟨0, 0, 0, -1, 0⟩ : WeierstrassCurve ℚ).Δ ^ g, fun e x hx => ?_⟩
  · obtain ⟨-, h, -⟩ := hy
    rw [← h, h₁, Nat.mul_one]
  · obtain ⟨x₁, hx₁⟩ := exists_keyPB_ring y₁ e
    obtain ⟨⟨τ, M, a, b, c, hab, hc, -, hN⟩, -⟩ := KeyNormalExists.exists_normalAt hU x₁
    have hv₁ : Val x₁ (e (⟨0, 0, 0, -1, 0⟩ : WeierstrassCurve ℚ).Δ) :=
      ⟨τ, M, a, b, c, hab, hc, hN, (hval e x₁ τ M a b c hx₁ hab hc hN).symm⟩
    obtain ⟨x', hx'⟩ := exists_isKeyPow ℂ x₁ g hg
    have hpb := keyPB_of_isKeyPow ℚ ℂ e y₁ y x₁ x' g hx₁ hy hx'
    have hid : KeyPB x x' (RingHom.id ℂ) := KeyCancel.keyPB_cancel ℚ ℂ ℂ y x' x e (RingHom.id ℂ) hpb hx
    rw [map_pow]
    exact ((GlobalTheory.T.normalForms_eq_of_keyDataIso_complex x' x hid).1 _).1 (hv₁.pow hx')

end GlobalTheory.KeyFam
