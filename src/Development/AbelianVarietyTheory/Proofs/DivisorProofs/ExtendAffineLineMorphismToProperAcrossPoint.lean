module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.SplitTorusToAbelianVarietyConst
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.AffineLineExt

open Polynomial

theorem isPrincipalIdealRing_away {R : Type} [CommRing R] [IsPrincipalIdealRing R] (r : R) :
    IsPrincipalIdealRing (Localization.Away r) := ⟨fun J => by
  rw [← IsLocalization.map_under (Submonoid.powers r) (Localization.Away r) J]
  obtain ⟨a, ha⟩ := (IsPrincipalIdealRing.principal (J.under R)).principal
  rw [ha]
  exact ⟨⟨_, by rw [Ideal.submodule_span_eq, Ideal.map_span, Set.image_singleton]⟩⟩⟩

theorem extend : ∀ (k : Type) [Field k] (B : Over (Sp k)) [IsProper B.hom] [LocallyOfFinitePresentation B.hom] (P : Polynomial k) (c : k), P ≠ 0 → ∀ u : Sp (Localization.Away (P * (Polynomial.X - Polynomial.C c))) ⟶ B.left, u ≫ B.hom = spMap (algebraMap k (Localization.Away (P * (Polynomial.X - Polynomial.C c)))) → ∃ v : Sp (Localization.Away P) ⟶ B.left, v ≫ B.hom = spMap (algebraMap k (Localization.Away P)) ∧ spMap (IsLocalization.Away.awayToAwayRight (S := Localization.Away P) (P := Localization.Away (P * (Polynomial.X - Polynomial.C c))) P (Polynomial.X - Polynomial.C c)) ≫ v = u := by
  intro k _ B _ _ P c hP u hu
  have hQ0 : P * (X - C c) ≠ 0 := mul_ne_zero hP (X_sub_C_ne_zero c)
  haveI : IsDomain (Localization.Away P) :=
    IsLocalization.isDomain_localization (powers_le_nonZeroDivisors_of_noZeroDivisors hP)
  haveI : IsDomain (Localization.Away (P * (X - C c))) :=
    IsLocalization.isDomain_localization (powers_le_nonZeroDivisors_of_noZeroDivisors hQ0)
  haveI : IsPrincipalIdealRing (Localization.Away P) := isPrincipalIdealRing_away P
  have hφ : ∀ a : k[X], IsLocalization.Away.awayToAwayRight (S := Localization.Away P)
      (P := Localization.Away (P * (X - C c))) P (X - C c) (algebraMap k[X] (Localization.Away P) a) =
      algebraMap k[X] (Localization.Away (P * (X - C c))) a :=
    IsLocalization.Away.awayToAwayRight_eq P (X - C c)
  have hcomp : spMap (algebraMap k[X] (Localization.Away (P * (X - C c)))) =
      spMap (IsLocalization.Away.awayToAwayRight (S := Localization.Away P)
        (P := Localization.Away (P * (X - C c))) P (X - C c)) ≫
        spMap (algebraMap k[X] (Localization.Away P)) := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
    exact (RingHom.ext hφ).symm
  haveI : IsOpenImmersion (spMap (algebraMap k[X] (Localization.Away P))) :=
    IsOpenImmersion.of_isLocalization P
  haveI : IsOpenImmersion (spMap (IsLocalization.Away.awayToAwayRight (S := Localization.Away P)
        (P := Localization.Away (P * (X - C c))) P (X - C c)) ≫
        spMap (algebraMap k[X] (Localization.Away P))) := by
    rw [← hcomp]
    exact IsOpenImmersion.of_isLocalization (P * (X - C c))
  haveI := IsOpenImmersion.of_comp (spMap (IsLocalization.Away.awayToAwayRight
    (S := Localization.Away P) (P := Localization.Away (P * (X - C c))) P (X - C c)))
    (spMap (algebraMap k[X] (Localization.Away P)))
  haveI : B.left.IsSeparated := ⟨by
    rw [show terminal.from B.left = B.hom ≫ terminal.from (Sp k) from terminal.hom_ext _ _]
    infer_instance⟩
  have hu' : u ≫ B.hom = spMap (IsLocalization.Away.awayToAwayRight (S := Localization.Away P)
      (P := Localization.Away (P * (X - C c))) P (X - C c)) ≫ spMap (algebraMap k (Localization.Away P)) := by
    rw [hu, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
    ext a
    simp only [RingHom.comp_apply]
    rw [IsScalarTower.algebraMap_apply k k[X] (Localization.Away P), hφ,
      ← IsScalarTower.algebraMap_apply]
  obtain ⟨g, h1, h2⟩ := TorusConst.exists_extension (Z := Sp (Localization.Away P))
    (fun x => TorusConst.valuationRing_stalk (Localization.Away P) x) _
    (spMap (algebraMap k (Localization.Away P))) B.hom u hu'
  exact ⟨g, h2, h1⟩

end GlobalTheory.AffineLineExt
