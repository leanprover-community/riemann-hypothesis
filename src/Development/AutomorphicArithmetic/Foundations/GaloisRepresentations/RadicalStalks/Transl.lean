module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RadicalStalks.IsConst
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
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.ConjSeq GlobalTheory.UPel.HT GlobalTheory.UPel.HT.ES UpperTheory.Gal.Ord
open scoped TensorProduct

theorem UpperTheory.Gal.Ord.transl :
    ∀ (k : Type) [Field k] (A : Over (Sp k)) [GrpObj A] (σ : k →+* k) (ψ : A.left ⟶ A.left), SMor A σ ψ →
      (∀ v : epsR k ⟶ A, IsTangent v → IsConst (v.left ≫ ψ)) → ∀ v : epsR k ⟶ A, IsConst (v.left ≫ ψ) := by
  intro k _ A _ σ ψ m hT v
  let z : Sp k ⟶ Sp (DualNumber k) := spMap (TrivSqZeroExt.fstHom k k k).toRingHom
  let r : Sp (DualNumber k) ⟶ Sp k := spMap (algebraMap k (DualNumber k))
  have hq : spMap ((algebraMap k (DualNumber k)).comp (TrivSqZeroExt.fstHom k k k).toRingHom) = r ≫ z := by
    simp only [r, z, spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  have hzr : z ≫ r = 𝟙 _ := by
    have e : (TrivSqZeroExt.fstHom k k k).toRingHom.comp (algebraMap k (DualNumber k)) = RingHom.id k := by
      ext x; simp
    simp only [r, z, spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp, e]
    simp
  have hqq : (r ≫ z) ≫ r ≫ z = r ≫ z := by
    rw [Category.assoc, reassoc_of% hzr]
  let c : epsR k ⟶ epsR k := Over.homMk (r ≫ z) (by
    show (r ≫ z) ≫ r = r
    rw [Category.assoc, hzr, Category.comp_id])
  let zz : 𝟙_ (Over (Sp k)) ⟶ epsR k := Over.homMk z hzr
  have hzc : zz ≫ c = zz := Over.OverMorphism.ext (by
    show z ≫ r ≫ z = z
    rw [reassoc_of% hzr])
  let v0 : epsR k ⟶ A := c ≫ v
  let t : epsR k ⟶ A := v0⁻¹ * v
  have hvt : v = v0 * t := by simp [t]
  have hzt : zz ≫ t = 1 := by
    have a : zz ≫ v0 = zz ≫ v := by simp only [v0, ← Category.assoc, hzc]
    calc zz ≫ t = (zz ≫ v0⁻¹) * (zz ≫ v) := MonObj.comp_mul _ _ _
      _ = (zz ≫ v0⁻¹) * (zz ≫ v0) := by rw [a]
      _ = zz ≫ (v0⁻¹ * v0) := (MonObj.comp_mul _ _ _).symm
      _ = 1 := by rw [inv_mul_cancel, MonObj.comp_one]
  have htan : IsTangent t := by
    have e1 : (1 : 𝟙_ (Over (Sp k)) ⟶ A) = η[A] := by
      show toUnit _ ≫ η[A] = _
      rw [toUnit_unique (toUnit _) (𝟙 _), Category.id_comp]
    show z ≫ t.left = η[A].left
    rw [← e1, ← hzt]
    rfl
  let Y : Over (Sp k) := Over.mk ((epsR k).hom ≫ spMap σ)
  let Q : Y ⟶ Y := Over.homMk (r ≫ z) (by
    show (r ≫ z) ≫ r ≫ spMap σ = r ≫ spMap σ
    rw [Category.assoc, reassoc_of% hzr])
  let down (x : epsR k ⟶ A) : Y ⟶ A :=
    Over.homMk (x.left ≫ ψ) (by simp [Y, m.w])
  have down_mul (x y : epsR k ⟶ A) : down (x * y) = down x * down y :=
    Over.OverMorphism.ext (m.mul (epsR k) x y (down x) (down y) rfl rfl).symm
  have h0 : Q ≫ down v0 = down v0 := Over.OverMorphism.ext (by
    show (r ≫ z) ≫ ((r ≫ z) ≫ v.left) ≫ ψ = ((r ≫ z) ≫ v.left) ≫ ψ
    simp only [← Category.assoc]
    rw [show ((r ≫ z) ≫ r) ≫ z = r ≫ z by simpa using hqq])
  have h1 : Q ≫ down t = down t := Over.OverMorphism.ext (by
    have := hT t htan
    unfold IsConst at this
    rw [hq] at this
    exact this)
  have key : Q ≫ down v = down v := by
    rw [hvt, down_mul, MonObj.comp_mul, h0, h1]
  unfold IsConst
  rw [hq]
  exact congrArg (fun u => u.left) key
