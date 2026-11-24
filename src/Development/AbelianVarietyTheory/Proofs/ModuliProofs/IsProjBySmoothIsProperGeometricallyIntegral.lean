module

public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
public import Mathlib.AlgebraicGeometry.Geometrically.Integral
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ForallGeometricallyIntegralOfSmoothOfGeometrical
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.PolBaseChangeOfRelAmpleLocal
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.RelAmpleOfLocallyOnBase
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.VeryAmpleByOfRelAmple
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

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.AbLaw

namespace GlobalTheory.AmpleBaseChange

theorem relAmple_of_isPullback {S S' : Scheme.{0}} {B : Over S} [IsProper B.hom] {M : LB B.left}
    (hM : M.IsLB) (hA : Out.RelAmple B M) {t : S' ⟶ S} {X : Scheme.{0}} {π : X ⟶ B.left}
    {f : X ⟶ S'} (h : IsPullback π f B.hom t) : Out.RelAmple (Over.mk f) (M.pull π) := by
  have hp : IsProper (Over.mk f).hom := MorphismProperty.of_isPullback (P := @IsProper) h ‹_›
  refine AmpleLocal.relAmple_of_locally S' (Over.mk f) (M.pull π) (pull_isLB hM π)
    inferInstance inferInstance fun s => ?_
  obtain ⟨V, hV, hs, -⟩ := exists_isAffineOpen_mem_and_subset (X := S) (U := ⊤) (x := t s) trivial
  exact ⟨t ⁻¹ᵁ V, hs, PolBaseChange.relAmple_restrict (A' := Over.mk f) h hM hA V hV⟩

theorem isProjBy_smooth_isProper_geometricallyIntegral :
    ∀ (S : Scheme.{0}) (B : Over S) [GrpObj B] (M : LB B.left), IsAbelianScheme B → M.IsLB → Out.RelAmple B M → ∀ (R : Type) [CommRing R] (t : Spec (CommRingCat.of R) ⟶ S) (X : Scheme.{0}) (π : X ⟶ B.left) (f : X ⟶ Spec (CommRingCat.of R)), IsPullback π f B.hom t → IsProjBy f ∧ Smooth f ∧ IsProper f ∧ GeometricallyIntegral f := by
  intro S B _ M hB hM hA R _ t X π f h
  have := hB.proper
  have hs : Smooth f := MorphismProperty.of_isPullback (P := @Smooth) h hB.smooth
  refine ⟨?_, hs, MorphismProperty.of_isPullback (P := @IsProper) h hB.proper,
    forall_geometricallyIntegral_of_smooth_of_geometricallyConnected _ _ f hs
      (MorphismProperty.of_isPullback (P := @GeometricallyConnected) h hB.geomConnected)⟩
  obtain ⟨N, -, m, s, hN, hv⟩ := veryAmpleBy_of_relAmple (A := Over.mk f) (pull_isLB hM π)
    (relAmple_of_isPullback hM hA h) (𝟙 X) (Category.id_comp f) (pull_isLB hM π)
    (LBIso.chartPull (chartPullId _) (chartPullPull (M.pull π) (𝟙 X) (𝟙 X) rfl)
      (PolBaseChange.lbIso_refl (pull_isLB hM π)))
  exact ⟨_, hN, m, s, hv⟩

end GlobalTheory.AmpleBaseChange
