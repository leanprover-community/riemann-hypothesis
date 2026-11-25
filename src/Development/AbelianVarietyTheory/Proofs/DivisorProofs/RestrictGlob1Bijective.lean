module

public import Development.AbelianVarietyTheory.Definitions.Divisors.CechDeRhamCoefMapOneFormsRestrictAlongFunctor
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
import Mathlib.Topology.Sheaves.Init
import Mathlib.Topology.Sheaves.Presheaf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.CubeSymmetricSwapFirst

@[expose] public section

open CategoryTheory AlgebraicGeometry KaehlerDifferential ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.CechDR

noncomputable section

namespace GlobalTheory

theorem restrict_glob1_bijective : ∀ {R : Type} [CommRing R] {C : Type} [Category.{0} C] {C' : Type} [Category.{0} C'] (F : C ⥤ CommAlgCat.{0} R) (G : C' ⥤ C), (∀ (T : C) (ω : Ω[F.obj T⁄R]), (∀ t (u : T ⟶ G.obj t), p1 F u ω = 0) → ω = 0) → (∀ (T : C) (s : ∀ t, (T ⟶ G.obj t) → Ω[F.obj (G.obj t)⁄R]), (∀ t t' (u : T ⟶ G.obj t) (a : t ⟶ t'), s t' (u ≫ G.map a) = p1 F (G.map a) (s t u)) → ∃ ω : Ω[F.obj T⁄R], ∀ t u, p1 F u ω = s t u) → Function.Bijective (pullGlob1 (CoefMap.restrict F G)) := by
  intro R _ C _ C' _ F G hsep hglue
  refine ⟨?_, ?_⟩
  · rw [injective_iff_map_eq_zero]
    intro ω hω
    apply Subtype.ext
    funext T
    refine hsep T (ω.1 T) fun t u ↦ ?_
    have h1 := congrArg (fun x : Glob1 (G ⋙ F) ↦ x.1 t) hω
    have h2 : (pullGlob1 (CoefMap.restrict F G) ω).1 t = ω.1 (G.obj t) := cechDeRhamCoefMapOneForms_restrictAlongFunctor F G t _
    rw [← ω.2 u, ← h2, h1]
    rfl
  · intro ω'
    have hc : ∀ (T : C), ∃ ω : Ω[F.obj T⁄R], ∀ t (u : T ⟶ G.obj t), p1 F u ω = ω'.1 t :=
      fun T ↦ hglue T (fun t _ ↦ ω'.1 t) fun t t' u a ↦ ω'.2 a
    choose ω hω using hc
    have hglob : ω ∈ Glob1 F := by
      intro T T' φ
      rw [← sub_eq_zero]
      refine hsep T' _ fun t u ↦ ?_
      rw [map_sub, ← oneFormsMapOfFunctorMorphism_comp, hω, hω, sub_self]
    refine ⟨⟨ω, hglob⟩, Subtype.ext (funext fun t ↦ ?_)⟩
    change q1 (CoefMap.restrict F G) t (ω (G.obj t)) = ω'.1 t
    rw [cechDeRhamCoefMapOneForms_restrictAlongFunctor, ← hω (G.obj t) t (𝟙 _), oneFormsMapOfFunctorMorphism_id]

end GlobalTheory
