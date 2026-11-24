module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Clauses
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
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsNatDiagIffIsDiag
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SumMulEqZeroOfSumToReal
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUnifOfIsMumfordOf
import Development.AbelianVarietyTheory.Definitions.Divisors.FromBase
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HomExtNormalSt
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.SiegelToroidalIntegral
import Mathlib.CategoryTheory.Monoidal.Opposite.Mon

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
namespace GlobalTheory.GrpPB

theorem isGrpPullback_comp {S S' T : Scheme.{0}} {G : Over S} [GrpObj G] {G' : Over S'} [GrpObj G']
    {P : Over T} [GrpObj P] {f : S' ⟶ S} {t : T ⟶ S'} {φ : G'.left ⟶ G.left} {ψ : P.left ⟶ G'.left}
    (h₁ : IsGrpPullback P G' t ψ) (h₂ : IsGrpPullback G' G f φ) :
    IsGrpPullback P G (t ≫ f) (ψ ≫ φ) := by
  refine ⟨h₁.1.paste_horiz h₂.1, fun T₀ x y x₀ y₀ hx hy => ?_⟩
  have wx : ∀ z : T₀ ⟶ P, (z.left ≫ ψ) ≫ G'.hom = (Over.mk (T₀.hom ≫ t)).hom := fun z => by
    rw [Category.assoc, h₁.1.w, ← Category.assoc, Over.w z]; rfl
  let x' : Over.mk (T₀.hom ≫ t) ⟶ G' := Over.homMk (x.left ≫ ψ) (wx x)
  let y' : Over.mk (T₀.hom ≫ t) ⟶ G' := Over.homMk (y.left ≫ ψ) (wx y)
  have e₁ : (x' * y').left = (x * y).left ≫ ψ := h₁.2 T₀ x y x' y' rfl rfl
  let e : Over.mk ((Over.mk (T₀.hom ≫ t)).hom ≫ f) ⟶ Over.mk (T₀.hom ≫ t ≫ f) :=
    Over.homMk (𝟙 _) (by simp)
  have e₂ : ((e ≫ x₀) * (e ≫ y₀)).left = (x' * y').left ≫ φ :=
    h₂.2 _ x' y' (e ≫ x₀) (e ≫ y₀) (by simp [e, x', hx]) (by simp [e, y', hy])
  rw [← MonObj.comp_mul, Over.comp_left] at e₂
  simp only [e, Over.homMk_left, Category.id_comp] at e₂
  rw [e₂, e₁, Category.assoc]

theorem baseChange_square {S S' T : Scheme.{0}} (G : Over S) [GrpObj G] (G' : Over S') [GrpObj G']
    (f : S' ⟶ S) (φ : G'.left ⟶ G.left) (h : IsGrpPullback G' G f φ) (t : T ⟶ S') :
    IsGrpPullback ((Over.pullback t).obj G') G (t ≫ f) (pullback.fst G'.hom t ≫ φ) ∧
      ∃ φ₂ : (G2 ((Over.pullback t).obj G')).left ⟶ (G2 G).left, IsSquare (pullback.fst G'.hom t ≫ φ) φ₂ := by
  have hc := isGrpPullback_comp (isGrpPullback_pullback G' t) h
  refine ⟨hc, ?_⟩
  set P := (Over.pullback t).obj G'
  have w : ∀ q : P ⊗ P ⟶ P, (q.left ≫ pullback.fst G'.hom t ≫ φ) ≫ G.hom = (Over.mk ((P ⊗ P).hom ≫ t ≫ f)).hom :=
    fun q => by
      rw [Category.assoc, Category.assoc, ← Category.assoc _ φ, hc.1.w, ← Category.assoc, Over.w q]; rfl
  let a : Over.mk ((P ⊗ P).hom ≫ t ≫ f) ⟶ G := Over.homMk _ (w (fst P P))
  let b : Over.mk ((P ⊗ P).hom ≫ t ≫ f) ⟶ G := Over.homMk _ (w (snd P P))
  refine ⟨(lift a b).left, ?_, ?_⟩
  · rw [← Over.comp_left, lift_fst]; rfl
  · rw [← Over.comp_left, lift_snd]; rfl

end GlobalTheory.GrpPB
