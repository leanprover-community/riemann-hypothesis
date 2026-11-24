module

public import Development.AbelianVarietyTheory.Definitions.Degenerations.RigGen
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
import Mathlib.Tactic.NormNum.Prime
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical
open ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.UnitTheta

theorem torsion_descends {B V K L : Scheme.{0}} {A : Over B} {G : Over V} {H : Over K} [GrpObj A] [GrpObj G] [GrpObj H]
    {f : K ⟶ B} {j : K ⟶ V} {ψ : H.left ⟶ A.left} {π : H.left ⟶ G.left}
    (hA : IsGrpPullback H A f ψ) (hG : IsGrpPullback H G j π) (i : L ⟶ K) (n : ℕ)
    (hs : ∀ z : Over.mk (i ≫ f) ⟶ A, z ^ n = 1 → ∃ s : B ⟶ A.left, s ≫ A.hom = 𝟙 B ∧ (i ≫ f) ≫ s = z.left)
    (y : Over.mk (i ≫ j) ⟶ G) (hy : y ^ n = 1) : ∃ x : K ⟶ G.left, i ≫ x = y.left := by
  let y' : Over.mk i ⟶ H := Over.homMk (hG.1.lift y.left i (Over.w y)) (hG.1.lift_snd _ _ _)
  have e₁ : y'.left ≫ π = y.left := hG.1.lift_fst _ _ _
  have e₂ : pushHom hG (Over.mk i) y' = y := Over.OverMorphism.ext e₁
  have inj : Function.Injective (pushHom hG (Over.mk i)) := fun a b h => by
    apply Over.OverMorphism.ext
    apply hG.1.hom_ext
    · exact congrArg (fun z => z.left) h
    · rw [Over.w, Over.w]
  have e₃ : y' ^ n = 1 := inj (by rw [map_pow, e₂, map_one]; exact hy)
  obtain ⟨s, hs₁, hs₂⟩ := hs (pushHom hA (Over.mk i) y') (by rw [← map_pow, e₃, map_one])
  have w : (f ≫ s) ≫ A.hom = 𝟙 K ≫ f := by rw [Category.assoc, hs₁, Category.comp_id, Category.id_comp]
  refine ⟨hA.1.lift (f ≫ s) (𝟙 K) w ≫ π, ?_⟩
  rw [← e₁, ← Category.assoc]
  congr 1
  apply hA.1.hom_ext
  · rw [Category.assoc, hA.1.lift_fst, ← Category.assoc, hs₂]
    rfl
  · rw [Category.assoc, hA.1.lift_snd, Category.comp_id]
    exact (Over.w y').symm

theorem torsion_rational : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (u : ρ.UTest p y₀) (m : ℕ), m ∣ S.r * S.N → ∀ y : Over.mk (spMap (algebraMap (FractionRing u.V) (PadicAlgCl p)) ≫ jK u.V) ⟶ u.G, y ^ m = 1 → ∃ x : Sp (FractionRing u.V) ⟶ u.G.left, spMap (algebraMap (FractionRing u.V) (PadicAlgCl p)) ≫ x = y.left := by
  intro o Ω _ _ _ S ρ p _ y₀ u m hm y hy
  have := u.U.gen_hom
  have hA := ((isGrpPullback_of_iso u.U.gen).comp u.cart).congr (Category.id_comp _) rfl
  refine torsion_descends hA (isGrpPullback_pullback u.G (jK u.V)) _ (S.r * S.N) (fun z hz => ?_) y ?_
  · obtain ⟨a, ha, -⟩ := ρ.pt_bij (PadicAlgCl p) _ z hz
    exact ⟨(ρ.pt a).left, Over.w (ρ.pt a), congrArg (fun t => t.left) ha⟩
  · obtain ⟨c, hc⟩ := hm
    rw [hc, pow_mul, hy, one_pow]

end GlobalTheory.UnitTheta
