module

public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ExistsUnitFormLocalizationEtaleNbhd
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.CubeSymmetricSwapFirst

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar

noncomputable section
namespace GlobalTheory.CompanionTheory.Ar.BT.TorsionKilled

theorem pow_eq_one : ∀ (R : Type) [CommRing R] [IsDomain R] (T : Type) [CommGroup T] (Γ : BT.QFGroup R T) (S : Scheme.{0}) (G : Over S) [GrpObj G] (x : Sp R ⟶ S) (N : ℕ) (i : Γ.G.left ⟶ G.left), Γ.IsTorsionAlong G x N i → ∀ t : T, t ^ N = 1 := by
  intro R _ _ T _ Γ S G _ x N i h t
  let lift : (genPt R ⟶ Γ.G) → (Over.mk ((genPt R).hom ≫ x) ⟶ G) := fun y =>
    Over.homMk (y.left ≫ i) (by
      have w := Over.w y
      simp only [Over.mk_hom, Category.assoc, h.isOver]
      rw [← Category.assoc, w]
      rfl)
  have lift_left : ∀ y, (lift y).left = y.left ≫ i := fun y => rfl
  have lift_mul : ∀ y z, lift (y * z) = lift y * lift z := fun y z => by
    ext1
    rw [h.mul (genPt R) y z (lift y) (lift z) rfl rfl]
    rfl
  have lift_one : lift 1 = 1 := by
    have e : lift 1 * lift 1 = lift 1 := by rw [← lift_mul, _root_.mul_one]
    exact mul_eq_left.mp e
  let L : (genPt R ⟶ Γ.G) →* (Over.mk ((genPt R).hom ≫ x) ⟶ G) :=
    { toFun := lift, map_one' := lift_one, map_mul' := lift_mul }
  have hk : lift (Γ.pt t) ^ N = 1 := (h.kernel (genPt R) (lift (Γ.pt t))).2 ⟨Γ.pt t, rfl⟩
  have hL : L (Γ.pt t ^ N) = L 1 := by
    rw [map_pow, map_one]
    exact hk
  have hy : Γ.pt t ^ N = 1 := h.inj (genPt R) _ _ (by
    have := congrArg (fun g : Over.mk ((genPt R).hom ≫ x) ⟶ G => g.left) hL
    exact this)
  have hp : Γ.pt (t ^ N) = Γ.pt 1 := by rw [map_pow, map_one, hy]
  let c : Spec (CommRingCat.of (FractionRing R)) := IsLocalRing.closedPoint (FractionRing R)
  exact Γ.pt_inj (t ^ N) 1 c c (by rw [hp])

end GlobalTheory.CompanionTheory.Ar.BT.TorsionKilled
