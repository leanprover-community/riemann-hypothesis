module

public import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.IsIntegralOfSmoothFieldOfConnectedSpace
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.LocallyQuasiFiniteOfQuasiFiniteAt
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsFiniteKerOfSurjPointsSameDimension
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.AlgClosed.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.CategoryTheory.Limits.Shapes.Connected
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
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
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaCore

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS

namespace GlobalTheory.SS

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry in
open scoped CategoryTheory.Obj in
theorem _root_.GlobalTheory.SS.finite_ker_of_surjective_points : ∀ (k : Type) [Field k] [IsAlgClosed k]
    (G : Over (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp k)) [GrpObj G], _root_.GlobalTheory.SS.SmConn G → ∀ f : G ⟶ G, IsMonHom f →
    (∀ y : (𝟙_ (Over (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp k)) ⟶ G), ∃ x : (𝟙_ (Over (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp k)) ⟶ G), x ≫ f = y) →
    Finite {x : (𝟙_ (Over (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp k)) ⟶ G) // x ≫ f = 1} := by
  intro k _ _ G _ hG f _ hpts
  have hG0 := hG
  unfold _root_.GlobalTheory.SS.SmConn at hG0
  obtain ⟨-, hsm, -, -, hgc⟩ := hG0
  have : Subsingleton (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp k) := inferInstanceAs (Subsingleton (Spec (CommRingCat.of k)))
  have : Nonempty (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp k) := inferInstanceAs (Nonempty (Spec (CommRingCat.of k)))
  have : ConnectedSpace G.left := GeometricallyConnected.connectedSpace_of_subsingleton G.hom
  obtain ⟨g, hg⟩ := _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.exists_dim_of_preconnected G.hom ((η[G] : 𝟙_ _ ⟶ G).left (IsLocalRing.closedPoint k))
  have hK := isFinite_ker_of_surjective_points_of_dim_eq k G G g hG hG hg hg f inferInstance hpts
  have hKhom : (pullback f (η[G] : 𝟙_ _ ⟶ G)).hom = (pullback.snd f (η[G] : 𝟙_ _ ⟶ G)).left := by
    rw [← Over.w (pullback.snd f (η[G] : 𝟙_ _ ⟶ G))]; rfl
  have : IsFinite (pullback f (η[G] : 𝟙_ _ ⟶ G)).hom := hKhom ▸ hK
  have hfin : Finite (pullback f (η[G] : 𝟙_ _ ⟶ G)).left := by
    have h := (pullback f (η[G] : 𝟙_ _ ⟶ G)).hom.finite_preimage_singleton
      (IsLocalRing.closedPoint k : Spec (CommRingCat.of k))
    exact Set.finite_univ_iff.mp
      (h.subset fun p _ => Set.mem_singleton_iff.mpr (Subsingleton.elim _ _))
  have hone : ∀ x : {x : (𝟙_ (Over (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp k)) ⟶ G) // x ≫ f = 1},
      x.1 ≫ f = 𝟙 _ ≫ (η[G] : 𝟙_ _ ⟶ G) := fun x => by
    rw [x.2, Category.id_comp]; rfl
  refine Finite.of_injective (fun x => (pullback.lift x.1 (𝟙 _) (hone x)).left
    (IsLocalRing.closedPoint k : Spec (CommRingCat.of k))) ?_
  intro x y hxy
  have : LocallyOfFiniteType (𝟙_ (Over (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp k))).hom :=
    inferInstanceAs (LocallyOfFiniteType (𝟙 (Spec (CommRingCat.of k))))
  have : Subsingleton (𝟙_ (Over (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp k))).left :=
    inferInstanceAs (Subsingleton (Spec (CommRingCat.of k)))
  have : IsReduced (𝟙_ (Over (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp k))).left := inferInstanceAs (IsReduced (Spec (CommRingCat.of k)))
  have hl : (pullback.lift x.1 (𝟙 _) (hone x)).left = (pullback.lift y.1 (𝟙 _) (hone y)).left := by
    have : LocallyOfFiniteType ((pullback.lift x.1 (𝟙 _) (hone x)).left ≫
        (pullback f (η[G] : 𝟙_ _ ⟶ G)).hom) := by rw [Over.w]; infer_instance
    refine ext_of_apply_eq (K := k) (pullback f (η[G] : 𝟙_ _ ⟶ G)).hom Set.univ
      isClosed_univ.isLocallyClosed dense_univ (fun p _ _ => ?_) ((Over.w _).trans (Over.w _).symm)
    obtain rfl := Subsingleton.elim p (IsLocalRing.closedPoint k : Spec (CommRingCat.of k))
    exact hxy
  have hl' : pullback.lift x.1 (𝟙 _) (hone x) = pullback.lift y.1 (𝟙 _) (hone y) := Over.OverMorphism.ext hl
  apply Subtype.ext
  have := congrArg (· ≫ pullback.fst f (η[G] : 𝟙_ _ ⟶ G)) hl'
  rw [pullback.lift_fst, pullback.lift_fst] at this
  exact this

end GlobalTheory.SS
