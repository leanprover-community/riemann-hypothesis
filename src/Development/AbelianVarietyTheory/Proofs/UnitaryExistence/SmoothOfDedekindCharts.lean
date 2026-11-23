module

public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Mathlib.RingTheory.DedekindDomain.Basic
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.SmoothOfIsDedekindDomain
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.NonzeroLocus
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.CubeSymmetricSwapFirst

@[expose] public section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap)
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw

namespace GlobalTheory.CurveThrough

theorem smooth_of_dedekind_charts (k : Type) [Field k] [IsAlgClosed k] (C : Scheme.{0})
    (f : C ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType f]
    (h : ∀ U : C.Opens, IsAffineOpen U → Nonempty U → IsDedekindDomain Γ(C, U)) :
    Smooth f := by
  refine HasRingHomProperty.of_iSup_eq_top (P := @Smooth)
    (fun U : {U : C.affineOpens // Nonempty U.1} => U.1) ?_ ?_
  · rw [eq_top_iff]
    intro x _
    obtain ⟨U, hU, hx, -⟩ := exists_isAffineOpen_mem_and_subset (U := ⊤) (x := x) trivial
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨⟨U, hU⟩, ⟨⟨x, hx⟩⟩⟩, hx⟩
  · rintro ⟨⟨U, hU⟩, hne⟩
    haveI := h U hU hne
    have hft : (f.appLE ⊤ U le_top).hom.FiniteType :=
      HasRingHomProperty.appLE @LocallyOfFiniteType f inferInstance ⟨⊤, isAffineOpen_top _⟩
        ⟨U, hU⟩ le_top
    let e := Scheme.ΓSpecIso (CommRingCat.of k)
    let φ : k →+* Γ(C, U) := (e.inv ≫ f.appLE ⊤ U le_top).hom
    have hφ : φ.FiniteType :=
      (RingHom.finiteType_respectsIso.cancel_left_isIso e.inv (f.appLE ⊤ U le_top)).2 hft
    have hs : φ.Smooth := by
      letI := φ.toAlgebra
      haveI : Algebra.FiniteType k Γ(C, U) := hφ
      exact GlobalTheory.DedekindSmooth.smooth_of_isDedekindDomain k Γ(C, U)
    exact (RingHom.Smooth.propertyIsLocal.respectsIso.cancel_left_isIso e.inv (f.appLE ⊤ U le_top)).1 hs

end GlobalTheory.CurveThrough
