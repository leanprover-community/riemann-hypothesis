module

public import Development.AbelianVarietyTheory.Definitions.Divisors.ComparisonMemCechHodgeFiltration
public import Mathlib.Algebra.DualNumber
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
import Mathlib.Tactic.Linter.HaveILetI
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

@[expose] public section

noncomputable section

open CategoryTheory AlgebraicGeometry KaehlerDifferential Opposite MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CechDR

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.InvForm

variable {R : Type} [CommRing R]

section Val

variable {B D : Type} [CommRing B] [Algebra R B] [CommRing D] [Algebra R D]

abbrev redHom (φ : B →ₐ[R] DualNumber D) : B →+* D :=
  (TrivSqZeroExt.fstHom R D D).toRingHom.comp φ.toRingHom

theorem redHom_algebraMap (φ : B →ₐ[R] DualNumber D) (r : R) :
    redHom φ (algebraMap R B r) = algebraMap R D r := by
  simp [redHom, TrivSqZeroExt.algebraMap_eq_inl']

def dVal (φ : B →ₐ[R] DualNumber D) : Ω[B⁄R] →ₗ[R] D :=
  letI : Algebra B D := (redHom φ).toAlgebra
  haveI : IsScalarTower R B D := IsScalarTower.of_algebraMap_eq fun r ↦ (redHom_algebraMap φ r).symm
  let d : Derivation R B D :=
    { toFun := fun b ↦ (φ b).snd
      map_add' := fun a b ↦ by simp
      map_smul' := fun r b ↦ by
        rw [map_smul, TrivSqZeroExt.snd_smul]
        rfl
      map_one_eq_zero' := by simp
      leibniz' := fun a b ↦ by
        change (φ (a * b)).snd = (φ a).fst * (φ b).snd + (φ b).fst * (φ a).snd
        rw [map_mul, TrivSqZeroExt.snd_mul]
        simp [MulOpposite.smul_eq_mul_unop]
        ring }
  d.liftKaehlerDifferential.restrictScalars R

theorem dVal_D (φ : B →ₐ[R] DualNumber D) (b : B) : dVal φ (KaehlerDifferential.D R B b) = (φ b).snd := by
  letI : Algebra B D := (redHom φ).toAlgebra
  haveI : IsScalarTower R B D := IsScalarTower.of_algebraMap_eq fun r ↦ (redHom_algebraMap φ r).symm
  exact Derivation.liftKaehlerDifferential_comp_D _ b

end Val

variable (A : Over (Sp R)) [GrpObj A]

def IsInv (w : GlobForm A.hom) : Prop :=
  ∀ (D : Type) [CommRing D] [Algebra R D] (U V : A.left.affineOpens)
    (φ : Sec A.hom U.1 →ₐ[R] DualNumber D) (ψ : Sec A.hom V.1 →ₐ[R] DualNumber D)
    (p q : Over.mk (spMap (algebraMap R (DualNumber D))) ⟶ A) (q₀ : Sp D ⟶ A.left),
    p.left = spMap (φ : Sec A.hom U.1 →+* DualNumber D) ≫ affPt A.hom U →
    q.left = spMap (algebraMap D (DualNumber D)) ≫ q₀ →
    (p * q).left = spMap (ψ : Sec A.hom V.1 →+* DualNumber D) ≫ affPt A.hom V →
    dVal φ (w.1 (op U)) = dVal ψ (w.1 (op V))

def InvForm : Submodule R (GlobForm A.hom) where
  carrier := {w | IsInv A w}
  add_mem' {w w'} hw hw' D _ _ U V φ ψ p q q₀ hp hq hpq := by
    change dVal φ (w.1 (op U) + w'.1 (op U)) = dVal ψ (w.1 (op V) + w'.1 (op V))
    rw [map_add (f := _), map_add (f := _), hw D U V φ ψ p q q₀ hp hq hpq, hw' D U V φ ψ p q q₀ hp hq hpq]
  zero_mem' D _ _ U V φ ψ p q q₀ _ _ _ := by
    change dVal φ 0 = dVal ψ 0
    rw [map_zero, map_zero]
  smul_mem' r w hw D _ _ U V φ ψ p q q₀ hp hq hpq := by
    change dVal φ (r • w.1 (op U)) = dVal ψ (r • w.1 (op V))
    rw [map_smul, map_smul, hw D U V φ ψ p q q₀ hp hq hpq]

end GlobalTheory.InvForm
