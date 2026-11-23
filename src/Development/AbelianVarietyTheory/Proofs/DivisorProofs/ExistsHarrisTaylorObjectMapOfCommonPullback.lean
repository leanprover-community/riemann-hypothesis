module

public import Development.AbelianVarietyTheory.Definitions.Divisors.NotCompactOfMEqOne
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.SiegelToroidalIntegral

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor

noncomputable section

namespace GlobalTheory.HTObjMap

theorem exists_objMap_of_common_pullback : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ) (S₀ : Scheme.{0}) (A₀ : Over S₀) [GrpObj A₀] (P₀ : LB (G2 A₀).left), P₀.IsLB → ∀ (T Z : Scheme.{0}) (t₁ : T ⟶ Sp R) (t₂ : Z ⟶ Sp R) (o : Obj b N t₁) (u : Obj b N t₂) (g : T ⟶ S₀) (πZ : Z ⟶ S₀) (z : T ⟶ Z) (φo : o.A.left ⟶ A₀.left) (φ₂o : (G2 o.A).left ⟶ (G2 A₀).left) (φu : u.A.left ⟶ A₀.left) (φ₂u : (G2 u.A).left ⟶ (G2 A₀).left) (ψ : o.A.left ⟶ u.A.left), IsGrpPullback o.A A₀ g φo → IsSquare φo φ₂o → LBIso o.P (P₀.pull φ₂o) → IsGrpPullback u.A A₀ πZ φu → IsSquare φu φ₂u → LBIso u.P (P₀.pull φ₂u) → z ≫ πZ = g → ψ ≫ φu = φo → ψ ≫ u.A.hom = o.A.hom ≫ z → (∀ a : D.O, (o.act.act a).left ≫ ψ = ψ ≫ (u.act.act a).left) → (∀ y, (o.eta y).left ≫ ψ = z ≫ (u.eta y).left) → ∃ m : ObjMap o u z, m.φ = ψ := by
  intro p _ D R _ b N S₀ A₀ _ P₀ hP₀ T Z t₁ t₂ o u g πZ z φo φ₂o φu φ₂u ψ ho sqo io hu squ iu hz hψ hw hact heta
  have cart : IsGrpPullback o.A u.A z ψ := IsGrpPullback.cancel hu (by rw [hz, hψ]; exact ho) hw
  have wc : ((fst o.A o.A).left ≫ ψ) ≫ u.A.hom = ((snd o.A o.A).left ≫ ψ) ≫ u.A.hom := by
    rw [Category.assoc, Category.assoc, hw, ← Category.assoc, ← Category.assoc, Over.w (fst o.A o.A), Over.w (snd o.A o.A)]
  let φ₂ : (G2 o.A).left ⟶ (G2 u.A).left := pullback.lift ((fst o.A o.A).left ≫ ψ) ((snd o.A o.A).left ≫ ψ) wc
  have s₁ : φ₂ ≫ (fst u.A u.A).left = (fst o.A o.A).left ≫ ψ := pullback.lift_fst _ _ _
  have s₂ : φ₂ ≫ (snd u.A u.A).left = (snd o.A o.A).left ≫ ψ := pullback.lift_snd _ _ _
  have sq : IsSquare ψ φ₂ := ⟨s₁, s₂⟩
  have a₁ : (φ₂ ≫ φ₂u) ≫ (fst A₀ A₀).left = φ₂o ≫ (fst A₀ A₀).left := by
    rw [Category.assoc, squ.1, ← Category.assoc, s₁, Category.assoc, hψ, sqo.1]
  have a₂ : (φ₂ ≫ φ₂u) ≫ (snd A₀ A₀).left = φ₂o ≫ (snd A₀ A₀).left := by
    rw [Category.assoc, squ.2, ← Category.assoc, s₂, Category.assoc, hψ, sqo.2]
  have e₂ : φ₂ ≫ φ₂u = φ₂o := Over.tensorObj_ext _ _ a₁ a₂
  have i₂ : LBIso (P₀.pull φ₂o) (u.P.pull φ₂) :=
    LBIso.chartPull (chartPullSame P₀ _ _ _ φ₂ (fun _ => e₂.symm)) (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull u.P φ₂ φ₂ rfl) (LBIso.symm iu)
  have pol : LBIso o.P (u.P.pull φ₂) :=
    LBIso.trans o.isLB (pull_isLB hP₀ _) (pull_isLB u.isLB _) io i₂
  exact ⟨{ φ := ψ, φ₂ := φ₂, cart := cart, sq := sq, act := hact, pol := pol, eta := heta }, rfl⟩

end GlobalTheory.HTObjMap
