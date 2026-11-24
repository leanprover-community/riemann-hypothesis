module

public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.DenseOfDenseP
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsThetaLevelAbelianSchemePullback
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ThetaLevelPullbackIdCompCancel
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
open GlobalTheory.ZM.NearBuild

noncomputable section
namespace GlobalTheory.ZM.NearBuild

open GlobalTheory.ThetaObjPull

theorem pow_left_comp_of_grpPullback {S S' : Scheme.{0}} {f : S' ⟶ S} {A : Over S} {A' : Over S'} [GrpObj A]
    [GrpObj A'] {φ : A'.left ⟶ A.left} (h : IsGrpPullback A' A f φ) (x' : Out.baseOver S' ⟶ A')
    (x : Out.baseOver S ⟶ A) (e : x'.left ≫ φ = f ≫ x.left) (n : ℕ) :
    (x' ^ n).left ≫ φ = f ≫ (x ^ n).left := by
  have e₁ : pushHom h _ x' = toBase f ≫ x := Over.OverMorphism.ext e
  have e₂ : pushHom h _ (x' ^ n) = toBase f ≫ (x ^ n) := by
    rw [map_pow, e₁]
    exact (map_pow (preHom (toBase f)) _ _).symm
  exact congrArg (fun z => z.left) e₂

theorem gLies_pull : ∀ (o : Type) [CommRing o] (g N' : ℕ) (J : Type) (b : TBase o (N' ^ 2)) (S S₁ S₂ : Scheme.{0}) (A : Over S) [GrpObj A] (L : LB A.left) (act : J → (A ⟶ A)) (Q : Fin (2 * g) → (Out.baseOver S ⟶ A)) (c : S₁ ⟶ S) (s₁ : S₁ ⟶ Sp o) (t₁ : TObj g (N' ^ 2) J b s₁) (ψ₁ : t₁.A.left ⟶ A.left) (y : S₂ ⟶ S₁) (s₂ : S₂ ⟶ Sp o), L.IsLB → GLies A act Q c t₁ ψ₁ → LBIso t₁.L (L.pull ψ₁) → y ≫ s₁ = s₂ → ∃ (u : TObj g (N' ^ 2) J b s₂) (ψ : u.A.left ⟶ A.left), TMap u t₁ y ∧ GLies A act Q (y ≫ c) u ψ ∧ LBIso u.L (L.pull ψ) ∧ ∀ i, (u.pt i).left ≫ ψ = y ≫ (t₁.pt i).left ≫ ψ₁ := by
  intro o _ g N' J b S S₁ S₂ A _ L act Q c s₁ t₁ ψ₁ y s₂ hL ⟨h₁, h₂, h₃⟩ hI hs
  obtain ⟨u, φ, k₁, k₂, k₃, k₄⟩ := GlobalTheory.tObj_pull o g (N' ^ 2) J b S₁ S₂ s₁ s₂ y t₁ hs
  refine ⟨u, φ ≫ ψ₁, ⟨φ, k₁, k₂, k₃, k₄⟩, ⟨k₁.comp h₁, fun i => ?_, fun i => ?_⟩, ?_, fun i => ?_⟩
  · rw [← Category.assoc, k₄, Category.assoc, h₂, Category.assoc]
  · rw [← Category.assoc, pow_left_comp_of_grpPullback k₁ _ _ (k₃ i), Category.assoc, h₃, Category.assoc]
  · exact LBIso.trans u.isLB (pull_isLB t₁.isLB _) (pull_isLB hL _) k₂ (lbIso_pull_comp hI φ)
  · rw [← Category.assoc, k₃, Category.assoc]

end GlobalTheory.ZM.NearBuild
end
